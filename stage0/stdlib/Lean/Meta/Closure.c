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
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
uint64_t l_Lean_Level_hash(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4_spec__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "assertion violation: !decl.isLet (allowNondep := true) -- should all be cdecls\n    "};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "_private.Lean.Meta.Closure.0.Lean.Meta.Closure.sortDecls.visit"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Meta.Closure"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "cycle detected in sorting abstracted variables"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Closure"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value),LEAN_SCALAR_PTR_LITERAL(248, 96, 54, 247, 94, 45, 114, 27)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Sorting decl "};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Sorted fvars: "};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9;
static const lean_string_object l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "MVars to abstract, topologically sorting the abstracted variables"};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10 = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__0;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__1;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosure___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__2;
static const lean_array_object l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__3 = (const lean_object*)&l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosure___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__4;
static const lean_string_object l_Lean_Meta_Closure_mkValueTypeClosure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.Closure.mkValueTypeClosure"};
static const lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__5 = (const lean_object*)&l_Lean_Meta_Closure_mkValueTypeClosure___closed__5_value;
static const lean_string_object l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 124, .m_capacity = 124, .m_length = 123, .m_data = "assertion violation: !value.hasFVar  -- In case https://github.com/leanprover/lean4/issues/10705 resurfaces in a new way\n  "};
static const lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__6 = (const lean_object*)&l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosure___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___closed__7;
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
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value),LEAN_SCALAR_PTR_LITERAL(249, 97, 222, 101, 51, 127, 178, 83)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(220, 178, 96, 6, 241, 231, 113, 20)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 127, 178, 186, 28, 24, 102, 169)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(21, 173, 206, 0, 127, 57, 105, 236)}};
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
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(12, 6, 147, 100, 167, 240, 247, 134)}};
static const lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10_value),LEAN_SCALAR_PTR_LITERAL(211, 133, 26, 59, 130, 208, 63, 13)}};
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
lean_object* v_visitedExpr_17_; lean_object* v_levelParams_18_; lean_object* v_nextLevelIdx_19_; lean_object* v_levelArgs_20_; lean_object* v_newLocalDecls_21_; lean_object* v_newLocalDeclsForMVars_22_; lean_object* v_newLetDecls_23_; lean_object* v_nextExprIdx_24_; lean_object* v_exprMVarArgs_25_; lean_object* v_exprFVarArgs_26_; lean_object* v_toProcess_27_; lean_object* v___y_28_; lean_object* v___y_29_; lean_object* v___y_34_; lean_object* v___y_35_; lean_object* v___y_36_; lean_object* v___y_49_; lean_object* v___y_50_; lean_object* v___y_51_; lean_object* v_i_52_; lean_object* v___y_58_; lean_object* v___y_59_; lean_object* v___y_60_; lean_object* v___y_61_; lean_object* v___y_62_; lean_object* v___y_72_; lean_object* v___y_73_; lean_object* v___y_74_; lean_object* v_i_75_; lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___y_83_; lean_object* v___y_84_; lean_object* v___y_85_; uint8_t v___x_155_; 
v___x_155_ = l_Lean_Level_hasMVar(v_u_8_);
if (v___x_155_ == 0)
{
uint8_t v___x_156_; 
v___x_156_ = l_Lean_Level_hasParam(v_u_8_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
lean_dec_ref(v_f_7_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v_u_8_);
return v___x_157_;
}
else
{
goto v___jp_95_;
}
}
else
{
goto v___jp_95_;
}
v___jp_16_:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_30_, 0, v___y_29_);
lean_ctor_set(v___x_30_, 1, v_visitedExpr_17_);
lean_ctor_set(v___x_30_, 2, v_levelParams_18_);
lean_ctor_set(v___x_30_, 3, v_nextLevelIdx_19_);
lean_ctor_set(v___x_30_, 4, v_levelArgs_20_);
lean_ctor_set(v___x_30_, 5, v_newLocalDecls_21_);
lean_ctor_set(v___x_30_, 6, v_newLocalDeclsForMVars_22_);
lean_ctor_set(v___x_30_, 7, v_newLetDecls_23_);
lean_ctor_set(v___x_30_, 8, v_nextExprIdx_24_);
lean_ctor_set(v___x_30_, 9, v_exprMVarArgs_25_);
lean_ctor_set(v___x_30_, 10, v_exprFVarArgs_26_);
lean_ctor_set(v___x_30_, 11, v_toProcess_27_);
v___x_31_ = lean_st_ref_put(v_a_10_, v___x_30_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___y_28_);
return v___x_32_;
}
v___jp_33_:
{
lean_object* v_visitedExpr_37_; lean_object* v_levelParams_38_; lean_object* v_nextLevelIdx_39_; lean_object* v_levelArgs_40_; lean_object* v_newLocalDecls_41_; lean_object* v_newLocalDeclsForMVars_42_; lean_object* v_newLetDecls_43_; lean_object* v_nextExprIdx_44_; lean_object* v_exprMVarArgs_45_; lean_object* v_exprFVarArgs_46_; lean_object* v_toProcess_47_; 
v_visitedExpr_37_ = lean_ctor_get(v___y_34_, 1);
lean_inc_ref(v_visitedExpr_37_);
v_levelParams_38_ = lean_ctor_get(v___y_34_, 2);
lean_inc_ref(v_levelParams_38_);
v_nextLevelIdx_39_ = lean_ctor_get(v___y_34_, 3);
lean_inc(v_nextLevelIdx_39_);
v_levelArgs_40_ = lean_ctor_get(v___y_34_, 4);
lean_inc_ref(v_levelArgs_40_);
v_newLocalDecls_41_ = lean_ctor_get(v___y_34_, 5);
lean_inc_ref(v_newLocalDecls_41_);
v_newLocalDeclsForMVars_42_ = lean_ctor_get(v___y_34_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_42_);
v_newLetDecls_43_ = lean_ctor_get(v___y_34_, 7);
lean_inc_ref(v_newLetDecls_43_);
v_nextExprIdx_44_ = lean_ctor_get(v___y_34_, 8);
lean_inc(v_nextExprIdx_44_);
v_exprMVarArgs_45_ = lean_ctor_get(v___y_34_, 9);
lean_inc_ref(v_exprMVarArgs_45_);
v_exprFVarArgs_46_ = lean_ctor_get(v___y_34_, 10);
lean_inc_ref(v_exprFVarArgs_46_);
v_toProcess_47_ = lean_ctor_get(v___y_34_, 11);
lean_inc_ref(v_toProcess_47_);
lean_dec_ref(v___y_34_);
v_visitedExpr_17_ = v_visitedExpr_37_;
v_levelParams_18_ = v_levelParams_38_;
v_nextLevelIdx_19_ = v_nextLevelIdx_39_;
v_levelArgs_20_ = v_levelArgs_40_;
v_newLocalDecls_21_ = v_newLocalDecls_41_;
v_newLocalDeclsForMVars_22_ = v_newLocalDeclsForMVars_42_;
v_newLetDecls_23_ = v_newLetDecls_43_;
v_nextExprIdx_24_ = v_nextExprIdx_44_;
v_exprMVarArgs_25_ = v_exprMVarArgs_45_;
v_exprFVarArgs_26_ = v_exprFVarArgs_46_;
v_toProcess_27_ = v_toProcess_47_;
v___y_28_ = v___y_35_;
v___y_29_ = v___y_36_;
goto v___jp_16_;
}
v___jp_48_:
{
lean_object* v_size_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_size_53_ = lean_ctor_get(v___y_50_, 0);
v___x_54_ = lean_unsigned_to_nat(1u);
v___x_55_ = lean_nat_add(v_size_53_, v___x_54_);
lean_inc(v___y_51_);
v___x_56_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_50_, v___x_55_, v_i_52_, v_u_8_, v___y_51_);
lean_dec(v_i_52_);
v___y_34_ = v___y_49_;
v___y_35_ = v___y_51_;
v___y_36_ = v___x_56_;
goto v___jp_33_;
}
v___jp_57_:
{
lean_object* v___x_63_; 
lean_inc(v_u_8_);
v___x_63_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___y_59_, v___y_61_, v___y_62_, v_u_8_);
switch(lean_obj_tag(v___x_63_))
{
case 0:
{
lean_object* v_index_64_; lean_object* v_size_65_; lean_object* v___x_66_; 
v_index_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_index_64_);
lean_dec_ref_known(v___x_63_, 3);
v_size_65_ = lean_ctor_get(v___y_62_, 0);
lean_inc(v_size_65_);
lean_inc(v___y_60_);
v___x_66_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_62_, v_size_65_, v_index_64_, v_u_8_, v___y_60_);
lean_dec(v_index_64_);
v___y_34_ = v___y_58_;
v___y_35_ = v___y_60_;
v___y_36_ = v___x_66_;
goto v___jp_33_;
}
case 1:
{
lean_object* v_index_67_; 
v_index_67_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_index_67_);
lean_dec_ref_known(v___x_63_, 1);
v___y_49_ = v___y_58_;
v___y_50_ = v___y_62_;
v___y_51_ = v___y_60_;
v_i_52_ = v_index_67_;
goto v___jp_48_;
}
default: 
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_62_, v___x_68_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_index_70_; 
v_index_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_index_70_);
lean_dec_ref_known(v___x_69_, 1);
v___y_49_ = v___y_58_;
v___y_50_ = v___y_62_;
v___y_51_ = v___y_60_;
v_i_52_ = v_index_70_;
goto v___jp_48_;
}
else
{
lean_dec(v_u_8_);
v___y_34_ = v___y_58_;
v___y_35_ = v___y_60_;
v___y_36_ = v___y_62_;
goto v___jp_33_;
}
}
}
}
v___jp_71_:
{
lean_object* v_size_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_size_76_ = lean_ctor_get(v___y_73_, 0);
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_add(v_size_76_, v___x_77_);
lean_inc(v___y_74_);
v___x_79_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_73_, v___x_78_, v_i_75_, v_u_8_, v___y_74_);
lean_dec(v_i_75_);
v___y_34_ = v___y_72_;
v___y_35_ = v___y_74_;
v___y_36_ = v___x_79_;
goto v___jp_33_;
}
v___jp_80_:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_inc_ref(v___y_84_);
lean_inc_ref(v___y_82_);
v___x_86_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___y_82_, v___y_84_, v___y_85_);
lean_inc(v_u_8_);
v___x_87_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___y_82_, v___y_84_, v___x_86_, v_u_8_);
switch(lean_obj_tag(v___x_87_))
{
case 0:
{
lean_object* v_index_88_; lean_object* v_size_89_; lean_object* v___x_90_; 
v_index_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_index_88_);
lean_dec_ref_known(v___x_87_, 3);
v_size_89_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_size_89_);
lean_inc(v___y_83_);
v___x_90_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_86_, v_size_89_, v_index_88_, v_u_8_, v___y_83_);
lean_dec(v_index_88_);
v___y_34_ = v___y_81_;
v___y_35_ = v___y_83_;
v___y_36_ = v___x_90_;
goto v___jp_33_;
}
case 1:
{
lean_object* v_index_91_; 
v_index_91_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_index_91_);
lean_dec_ref_known(v___x_87_, 1);
v___y_72_ = v___y_81_;
v___y_73_ = v___x_86_;
v___y_74_ = v___y_83_;
v_i_75_ = v_index_91_;
goto v___jp_71_;
}
default: 
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_86_, v___x_92_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_index_94_; 
v_index_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_index_94_);
lean_dec_ref_known(v___x_93_, 1);
v___y_72_ = v___y_81_;
v___y_73_ = v___x_86_;
v___y_74_ = v___y_83_;
v_i_75_ = v_index_94_;
goto v___jp_71_;
}
else
{
lean_dec(v_u_8_);
v___y_34_ = v___y_81_;
v___y_35_ = v___y_83_;
v___y_36_ = v___x_86_;
goto v___jp_33_;
}
}
}
}
v___jp_95_:
{
lean_object* v___x_96_; lean_object* v_visitedLevel_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_96_ = lean_st_ref_get(v_a_10_);
v_visitedLevel_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc_ref(v_visitedLevel_97_);
lean_dec(v___x_96_);
v___x_98_ = ((lean_object*)(l_Lean_Meta_Closure_visitLevel___closed__0));
v___x_99_ = ((lean_object*)(l_Lean_Meta_Closure_visitLevel___closed__1));
lean_inc(v_u_8_);
v___x_100_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_98_, v___x_99_, v_visitedLevel_97_, v_u_8_);
lean_dec_ref(v_visitedLevel_97_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_box(v_a_9_);
lean_inc(v_a_14_);
lean_inc_ref(v_a_13_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc(v_u_8_);
v___x_102_ = lean_apply_8(v_f_7_, v_u_8_, v___x_101_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, lean_box(0));
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_104_; lean_object* v_visitedLevel_105_; lean_object* v_visitedExpr_106_; lean_object* v_levelParams_107_; lean_object* v_nextLevelIdx_108_; lean_object* v_levelArgs_109_; lean_object* v_newLocalDecls_110_; lean_object* v_newLocalDeclsForMVars_111_; lean_object* v_newLetDecls_112_; lean_object* v_nextExprIdx_113_; lean_object* v_exprMVarArgs_114_; lean_object* v_exprFVarArgs_115_; lean_object* v_toProcess_116_; lean_object* v___x_117_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_102_, 1);
v___x_104_ = lean_st_ref_take(v_a_10_);
v_visitedLevel_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc_ref(v_visitedLevel_105_);
v_visitedExpr_106_ = lean_ctor_get(v___x_104_, 1);
lean_inc_ref(v_visitedExpr_106_);
v_levelParams_107_ = lean_ctor_get(v___x_104_, 2);
lean_inc_ref(v_levelParams_107_);
v_nextLevelIdx_108_ = lean_ctor_get(v___x_104_, 3);
lean_inc(v_nextLevelIdx_108_);
v_levelArgs_109_ = lean_ctor_get(v___x_104_, 4);
lean_inc_ref(v_levelArgs_109_);
v_newLocalDecls_110_ = lean_ctor_get(v___x_104_, 5);
lean_inc_ref(v_newLocalDecls_110_);
v_newLocalDeclsForMVars_111_ = lean_ctor_get(v___x_104_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_111_);
v_newLetDecls_112_ = lean_ctor_get(v___x_104_, 7);
lean_inc_ref(v_newLetDecls_112_);
v_nextExprIdx_113_ = lean_ctor_get(v___x_104_, 8);
lean_inc(v_nextExprIdx_113_);
v_exprMVarArgs_114_ = lean_ctor_get(v___x_104_, 9);
lean_inc_ref(v_exprMVarArgs_114_);
v_exprFVarArgs_115_ = lean_ctor_get(v___x_104_, 10);
lean_inc_ref(v_exprFVarArgs_115_);
v_toProcess_116_ = lean_ctor_get(v___x_104_, 11);
lean_inc_ref(v_toProcess_116_);
lean_inc(v_u_8_);
v___x_117_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_98_, v___x_99_, v_visitedLevel_105_, v_u_8_);
switch(lean_obj_tag(v___x_117_))
{
case 0:
{
lean_object* v_index_118_; lean_object* v_size_119_; lean_object* v___x_120_; 
lean_dec(v___x_104_);
v_index_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_index_118_);
lean_dec_ref_known(v___x_117_, 3);
v_size_119_ = lean_ctor_get(v_visitedLevel_105_, 0);
lean_inc(v_size_119_);
lean_inc(v_a_103_);
v___x_120_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_105_, v_size_119_, v_index_118_, v_u_8_, v_a_103_);
lean_dec(v_index_118_);
v_visitedExpr_17_ = v_visitedExpr_106_;
v_levelParams_18_ = v_levelParams_107_;
v_nextLevelIdx_19_ = v_nextLevelIdx_108_;
v_levelArgs_20_ = v_levelArgs_109_;
v_newLocalDecls_21_ = v_newLocalDecls_110_;
v_newLocalDeclsForMVars_22_ = v_newLocalDeclsForMVars_111_;
v_newLetDecls_23_ = v_newLetDecls_112_;
v_nextExprIdx_24_ = v_nextExprIdx_113_;
v_exprMVarArgs_25_ = v_exprMVarArgs_114_;
v_exprFVarArgs_26_ = v_exprFVarArgs_115_;
v_toProcess_27_ = v_toProcess_116_;
v___y_28_ = v_a_103_;
v___y_29_ = v___x_120_;
goto v___jp_16_;
}
case 1:
{
lean_object* v_index_121_; lean_object* v_size_122_; lean_object* v_keyArray_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_index_121_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_index_121_);
lean_dec_ref_known(v___x_117_, 1);
v_size_122_ = lean_ctor_get(v_visitedLevel_105_, 0);
v_keyArray_123_ = lean_ctor_get(v_visitedLevel_105_, 1);
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_add(v_size_122_, v___x_124_);
v___x_126_ = lean_array_get_size(v_keyArray_123_);
v___x_127_ = lean_nat_dec_lt(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_dec(v___x_125_);
lean_dec(v_index_121_);
lean_dec_ref(v_toProcess_116_);
lean_dec_ref(v_exprFVarArgs_115_);
lean_dec_ref(v_exprMVarArgs_114_);
lean_dec(v_nextExprIdx_113_);
lean_dec_ref(v_newLetDecls_112_);
lean_dec_ref(v_newLocalDeclsForMVars_111_);
lean_dec_ref(v_newLocalDecls_110_);
lean_dec_ref(v_levelArgs_109_);
lean_dec(v_nextLevelIdx_108_);
lean_dec_ref(v_levelParams_107_);
lean_dec_ref(v_visitedExpr_106_);
v___y_81_ = v___x_104_;
v___y_82_ = v___x_98_;
v___y_83_ = v_a_103_;
v___y_84_ = v___x_99_;
v___y_85_ = v_visitedLevel_105_;
goto v___jp_80_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_128_ = lean_unsigned_to_nat(4u);
v___x_129_ = lean_nat_mul(v___x_125_, v___x_128_);
v___x_130_ = lean_unsigned_to_nat(3u);
v___x_131_ = lean_nat_mul(v___x_126_, v___x_130_);
v___x_132_ = lean_nat_dec_le(v___x_129_, v___x_131_);
lean_dec(v___x_131_);
lean_dec(v___x_129_);
if (v___x_132_ == 0)
{
lean_dec(v___x_125_);
lean_dec(v_index_121_);
lean_dec_ref(v_toProcess_116_);
lean_dec_ref(v_exprFVarArgs_115_);
lean_dec_ref(v_exprMVarArgs_114_);
lean_dec(v_nextExprIdx_113_);
lean_dec_ref(v_newLetDecls_112_);
lean_dec_ref(v_newLocalDeclsForMVars_111_);
lean_dec_ref(v_newLocalDecls_110_);
lean_dec_ref(v_levelArgs_109_);
lean_dec(v_nextLevelIdx_108_);
lean_dec_ref(v_levelParams_107_);
lean_dec_ref(v_visitedExpr_106_);
v___y_81_ = v___x_104_;
v___y_82_ = v___x_98_;
v___y_83_ = v_a_103_;
v___y_84_ = v___x_99_;
v___y_85_ = v_visitedLevel_105_;
goto v___jp_80_;
}
else
{
lean_object* v___x_133_; 
lean_dec(v___x_104_);
lean_inc(v_a_103_);
v___x_133_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_105_, v___x_125_, v_index_121_, v_u_8_, v_a_103_);
lean_dec(v_index_121_);
v_visitedExpr_17_ = v_visitedExpr_106_;
v_levelParams_18_ = v_levelParams_107_;
v_nextLevelIdx_19_ = v_nextLevelIdx_108_;
v_levelArgs_20_ = v_levelArgs_109_;
v_newLocalDecls_21_ = v_newLocalDecls_110_;
v_newLocalDeclsForMVars_22_ = v_newLocalDeclsForMVars_111_;
v_newLetDecls_23_ = v_newLetDecls_112_;
v_nextExprIdx_24_ = v_nextExprIdx_113_;
v_exprMVarArgs_25_ = v_exprMVarArgs_114_;
v_exprFVarArgs_26_ = v_exprFVarArgs_115_;
v_toProcess_27_ = v_toProcess_116_;
v___y_28_ = v_a_103_;
v___y_29_ = v___x_133_;
goto v___jp_16_;
}
}
}
default: 
{
lean_object* v_size_134_; lean_object* v_keyArray_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
lean_dec_ref(v_toProcess_116_);
lean_dec_ref(v_exprFVarArgs_115_);
lean_dec_ref(v_exprMVarArgs_114_);
lean_dec(v_nextExprIdx_113_);
lean_dec_ref(v_newLetDecls_112_);
lean_dec_ref(v_newLocalDeclsForMVars_111_);
lean_dec_ref(v_newLocalDecls_110_);
lean_dec_ref(v_levelArgs_109_);
lean_dec(v_nextLevelIdx_108_);
lean_dec_ref(v_levelParams_107_);
lean_dec_ref(v_visitedExpr_106_);
v_size_134_ = lean_ctor_get(v_visitedLevel_105_, 0);
v_keyArray_135_ = lean_ctor_get(v_visitedLevel_105_, 1);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_size_134_, v___x_136_);
v___x_138_ = lean_array_get_size(v_keyArray_135_);
v___x_139_ = lean_nat_dec_lt(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
lean_dec(v___x_137_);
v___x_140_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_98_, v___x_99_, v_visitedLevel_105_);
v___y_58_ = v___x_104_;
v___y_59_ = v___x_98_;
v___y_60_ = v_a_103_;
v___y_61_ = v___x_99_;
v___y_62_ = v___x_140_;
goto v___jp_57_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_141_ = lean_unsigned_to_nat(4u);
v___x_142_ = lean_nat_mul(v___x_137_, v___x_141_);
lean_dec(v___x_137_);
v___x_143_ = lean_unsigned_to_nat(3u);
v___x_144_ = lean_nat_mul(v___x_138_, v___x_143_);
v___x_145_ = lean_nat_dec_le(v___x_142_, v___x_144_);
lean_dec(v___x_144_);
lean_dec(v___x_142_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_98_, v___x_99_, v_visitedLevel_105_);
v___y_58_ = v___x_104_;
v___y_59_ = v___x_98_;
v___y_60_ = v_a_103_;
v___y_61_ = v___x_99_;
v___y_62_ = v___x_146_;
goto v___jp_57_;
}
else
{
v___y_58_ = v___x_104_;
v___y_59_ = v___x_98_;
v___y_60_ = v_a_103_;
v___y_61_ = v___x_99_;
v___y_62_ = v_visitedLevel_105_;
goto v___jp_57_;
}
}
}
}
}
else
{
lean_dec(v_u_8_);
return v___x_102_;
}
}
else
{
lean_object* v_val_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec(v_u_8_);
lean_dec_ref(v_f_7_);
v_val_147_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_100_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_val_147_);
lean_dec(v___x_100_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
lean_ctor_set_tag(v___x_149_, 0);
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_val_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object* v_f_158_, lean_object* v_u_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
uint8_t v_a_boxed_167_; lean_object* v_res_168_; 
v_a_boxed_167_ = lean_unbox(v_a_160_);
v_res_168_ = l_Lean_Meta_Closure_visitLevel(v_f_158_, v_u_159_, v_a_boxed_167_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr(lean_object* v_f_171_, lean_object* v_e_172_, uint8_t v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___y_181_; lean_object* v___y_182_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v_i_211_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v_i_254_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; uint8_t v___x_344_; 
v___x_344_ = l_Lean_Expr_hasLevelParam(v_e_172_);
if (v___x_344_ == 0)
{
uint8_t v___x_345_; 
v___x_345_ = l_Lean_Expr_hasFVar(v_e_172_);
if (v___x_345_ == 0)
{
uint8_t v___x_346_; 
v___x_346_ = l_Lean_Expr_hasMVar(v_e_172_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_dec_ref(v_f_171_);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v_e_172_);
return v___x_347_;
}
else
{
goto v___jp_284_;
}
}
else
{
goto v___jp_284_;
}
}
else
{
goto v___jp_284_;
}
v___jp_180_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_194_, 0, v___y_190_);
lean_ctor_set(v___x_194_, 1, v___y_193_);
lean_ctor_set(v___x_194_, 2, v___y_185_);
lean_ctor_set(v___x_194_, 3, v___y_189_);
lean_ctor_set(v___x_194_, 4, v___y_184_);
lean_ctor_set(v___x_194_, 5, v___y_192_);
lean_ctor_set(v___x_194_, 6, v___y_181_);
lean_ctor_set(v___x_194_, 7, v___y_187_);
lean_ctor_set(v___x_194_, 8, v___y_183_);
lean_ctor_set(v___x_194_, 9, v___y_186_);
lean_ctor_set(v___x_194_, 10, v___y_191_);
lean_ctor_set(v___x_194_, 11, v___y_182_);
v___x_195_ = lean_st_ref_put(v_a_174_, v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___y_188_);
return v___x_196_;
}
v___jp_197_:
{
lean_object* v_size_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_size_212_ = lean_ctor_get(v___y_210_, 0);
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_add(v_size_212_, v___x_213_);
lean_inc_ref(v___y_205_);
v___x_215_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_210_, v___x_214_, v_i_211_, v_e_172_, v___y_205_);
lean_dec(v_i_211_);
v___y_181_ = v___y_198_;
v___y_182_ = v___y_199_;
v___y_183_ = v___y_200_;
v___y_184_ = v___y_201_;
v___y_185_ = v___y_202_;
v___y_186_ = v___y_203_;
v___y_187_ = v___y_204_;
v___y_188_ = v___y_205_;
v___y_189_ = v___y_206_;
v___y_190_ = v___y_207_;
v___y_191_ = v___y_208_;
v___y_192_ = v___y_209_;
v___y_193_ = v___x_215_;
goto v___jp_180_;
}
v___jp_216_:
{
lean_object* v___x_232_; 
lean_inc_ref(v_e_172_);
v___x_232_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___y_219_, v___y_217_, v___y_231_, v_e_172_);
switch(lean_obj_tag(v___x_232_))
{
case 0:
{
lean_object* v_index_233_; lean_object* v_size_234_; lean_object* v___x_235_; 
v_index_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_index_233_);
lean_dec_ref_known(v___x_232_, 3);
v_size_234_ = lean_ctor_get(v___y_231_, 0);
lean_inc(v_size_234_);
lean_inc_ref(v___y_226_);
v___x_235_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_231_, v_size_234_, v_index_233_, v_e_172_, v___y_226_);
lean_dec(v_index_233_);
v___y_181_ = v___y_218_;
v___y_182_ = v___y_220_;
v___y_183_ = v___y_221_;
v___y_184_ = v___y_223_;
v___y_185_ = v___y_222_;
v___y_186_ = v___y_224_;
v___y_187_ = v___y_225_;
v___y_188_ = v___y_226_;
v___y_189_ = v___y_227_;
v___y_190_ = v___y_228_;
v___y_191_ = v___y_229_;
v___y_192_ = v___y_230_;
v___y_193_ = v___x_235_;
goto v___jp_180_;
}
case 1:
{
lean_object* v_index_236_; 
v_index_236_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_index_236_);
lean_dec_ref_known(v___x_232_, 1);
v___y_198_ = v___y_218_;
v___y_199_ = v___y_220_;
v___y_200_ = v___y_221_;
v___y_201_ = v___y_223_;
v___y_202_ = v___y_222_;
v___y_203_ = v___y_224_;
v___y_204_ = v___y_225_;
v___y_205_ = v___y_226_;
v___y_206_ = v___y_227_;
v___y_207_ = v___y_228_;
v___y_208_ = v___y_229_;
v___y_209_ = v___y_230_;
v___y_210_ = v___y_231_;
v_i_211_ = v_index_236_;
goto v___jp_197_;
}
default: 
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_231_, v___x_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_index_239_; 
v_index_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_index_239_);
lean_dec_ref_known(v___x_238_, 1);
v___y_198_ = v___y_218_;
v___y_199_ = v___y_220_;
v___y_200_ = v___y_221_;
v___y_201_ = v___y_223_;
v___y_202_ = v___y_222_;
v___y_203_ = v___y_224_;
v___y_204_ = v___y_225_;
v___y_205_ = v___y_226_;
v___y_206_ = v___y_227_;
v___y_207_ = v___y_228_;
v___y_208_ = v___y_229_;
v___y_209_ = v___y_230_;
v___y_210_ = v___y_231_;
v_i_211_ = v_index_239_;
goto v___jp_197_;
}
else
{
lean_dec_ref(v_e_172_);
v___y_181_ = v___y_218_;
v___y_182_ = v___y_220_;
v___y_183_ = v___y_221_;
v___y_184_ = v___y_223_;
v___y_185_ = v___y_222_;
v___y_186_ = v___y_224_;
v___y_187_ = v___y_225_;
v___y_188_ = v___y_226_;
v___y_189_ = v___y_227_;
v___y_190_ = v___y_228_;
v___y_191_ = v___y_229_;
v___y_192_ = v___y_230_;
v___y_193_ = v___y_231_;
goto v___jp_180_;
}
}
}
}
v___jp_240_:
{
lean_object* v_size_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_size_255_ = lean_ctor_get(v___y_248_, 0);
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_add(v_size_255_, v___x_256_);
lean_inc_ref(v___y_249_);
v___x_258_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_248_, v___x_257_, v_i_254_, v_e_172_, v___y_249_);
lean_dec(v_i_254_);
v___y_181_ = v___y_241_;
v___y_182_ = v___y_242_;
v___y_183_ = v___y_243_;
v___y_184_ = v___y_245_;
v___y_185_ = v___y_244_;
v___y_186_ = v___y_246_;
v___y_187_ = v___y_247_;
v___y_188_ = v___y_249_;
v___y_189_ = v___y_250_;
v___y_190_ = v___y_251_;
v___y_191_ = v___y_252_;
v___y_192_ = v___y_253_;
v___y_193_ = v___x_258_;
goto v___jp_180_;
}
v___jp_259_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_inc_ref(v___y_260_);
lean_inc_ref(v___y_262_);
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___y_262_, v___y_260_, v___y_265_);
lean_inc_ref(v_e_172_);
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___y_262_, v___y_260_, v___x_275_, v_e_172_);
switch(lean_obj_tag(v___x_276_))
{
case 0:
{
lean_object* v_index_277_; lean_object* v_size_278_; lean_object* v___x_279_; 
v_index_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_index_277_);
lean_dec_ref_known(v___x_276_, 3);
v_size_278_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_size_278_);
lean_inc_ref(v___y_270_);
v___x_279_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_275_, v_size_278_, v_index_277_, v_e_172_, v___y_270_);
lean_dec(v_index_277_);
v___y_181_ = v___y_261_;
v___y_182_ = v___y_263_;
v___y_183_ = v___y_264_;
v___y_184_ = v___y_266_;
v___y_185_ = v___y_267_;
v___y_186_ = v___y_268_;
v___y_187_ = v___y_269_;
v___y_188_ = v___y_270_;
v___y_189_ = v___y_271_;
v___y_190_ = v___y_272_;
v___y_191_ = v___y_273_;
v___y_192_ = v___y_274_;
v___y_193_ = v___x_279_;
goto v___jp_180_;
}
case 1:
{
lean_object* v_index_280_; 
v_index_280_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_index_280_);
lean_dec_ref_known(v___x_276_, 1);
v___y_241_ = v___y_261_;
v___y_242_ = v___y_263_;
v___y_243_ = v___y_264_;
v___y_244_ = v___y_267_;
v___y_245_ = v___y_266_;
v___y_246_ = v___y_268_;
v___y_247_ = v___y_269_;
v___y_248_ = v___x_275_;
v___y_249_ = v___y_270_;
v___y_250_ = v___y_271_;
v___y_251_ = v___y_272_;
v___y_252_ = v___y_273_;
v___y_253_ = v___y_274_;
v_i_254_ = v_index_280_;
goto v___jp_240_;
}
default: 
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_275_, v___x_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_index_283_; 
v_index_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_index_283_);
lean_dec_ref_known(v___x_282_, 1);
v___y_241_ = v___y_261_;
v___y_242_ = v___y_263_;
v___y_243_ = v___y_264_;
v___y_244_ = v___y_267_;
v___y_245_ = v___y_266_;
v___y_246_ = v___y_268_;
v___y_247_ = v___y_269_;
v___y_248_ = v___x_275_;
v___y_249_ = v___y_270_;
v___y_250_ = v___y_271_;
v___y_251_ = v___y_272_;
v___y_252_ = v___y_273_;
v___y_253_ = v___y_274_;
v_i_254_ = v_index_283_;
goto v___jp_240_;
}
else
{
lean_dec_ref(v_e_172_);
v___y_181_ = v___y_261_;
v___y_182_ = v___y_263_;
v___y_183_ = v___y_264_;
v___y_184_ = v___y_266_;
v___y_185_ = v___y_267_;
v___y_186_ = v___y_268_;
v___y_187_ = v___y_269_;
v___y_188_ = v___y_270_;
v___y_189_ = v___y_271_;
v___y_190_ = v___y_272_;
v___y_191_ = v___y_273_;
v___y_192_ = v___y_274_;
v___y_193_ = v___x_275_;
goto v___jp_180_;
}
}
}
}
v___jp_284_:
{
lean_object* v___x_285_; lean_object* v_visitedExpr_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_285_ = lean_st_ref_get(v_a_174_);
v_visitedExpr_286_ = lean_ctor_get(v___x_285_, 1);
lean_inc_ref(v_visitedExpr_286_);
lean_dec(v___x_285_);
v___x_287_ = ((lean_object*)(l_Lean_Meta_Closure_visitExpr___closed__0));
v___x_288_ = ((lean_object*)(l_Lean_Meta_Closure_visitExpr___closed__1));
lean_inc_ref(v_e_172_);
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_287_, v___x_288_, v_visitedExpr_286_, v_e_172_);
lean_dec_ref(v_visitedExpr_286_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_box(v_a_173_);
lean_inc(v_a_178_);
lean_inc_ref(v_a_177_);
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc(v_a_174_);
lean_inc_ref(v_e_172_);
v___x_291_ = lean_apply_8(v_f_171_, v_e_172_, v___x_290_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, lean_box(0));
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_293_; lean_object* v_visitedLevel_294_; lean_object* v_visitedExpr_295_; lean_object* v_levelParams_296_; lean_object* v_nextLevelIdx_297_; lean_object* v_levelArgs_298_; lean_object* v_newLocalDecls_299_; lean_object* v_newLocalDeclsForMVars_300_; lean_object* v_newLetDecls_301_; lean_object* v_nextExprIdx_302_; lean_object* v_exprMVarArgs_303_; lean_object* v_exprFVarArgs_304_; lean_object* v_toProcess_305_; lean_object* v___x_306_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v___x_291_, 1);
v___x_293_ = lean_st_ref_take(v_a_174_);
v_visitedLevel_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc_ref(v_visitedLevel_294_);
v_visitedExpr_295_ = lean_ctor_get(v___x_293_, 1);
lean_inc_ref(v_visitedExpr_295_);
v_levelParams_296_ = lean_ctor_get(v___x_293_, 2);
lean_inc_ref(v_levelParams_296_);
v_nextLevelIdx_297_ = lean_ctor_get(v___x_293_, 3);
lean_inc(v_nextLevelIdx_297_);
v_levelArgs_298_ = lean_ctor_get(v___x_293_, 4);
lean_inc_ref(v_levelArgs_298_);
v_newLocalDecls_299_ = lean_ctor_get(v___x_293_, 5);
lean_inc_ref(v_newLocalDecls_299_);
v_newLocalDeclsForMVars_300_ = lean_ctor_get(v___x_293_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_300_);
v_newLetDecls_301_ = lean_ctor_get(v___x_293_, 7);
lean_inc_ref(v_newLetDecls_301_);
v_nextExprIdx_302_ = lean_ctor_get(v___x_293_, 8);
lean_inc(v_nextExprIdx_302_);
v_exprMVarArgs_303_ = lean_ctor_get(v___x_293_, 9);
lean_inc_ref(v_exprMVarArgs_303_);
v_exprFVarArgs_304_ = lean_ctor_get(v___x_293_, 10);
lean_inc_ref(v_exprFVarArgs_304_);
v_toProcess_305_ = lean_ctor_get(v___x_293_, 11);
lean_inc_ref(v_toProcess_305_);
lean_dec(v___x_293_);
lean_inc_ref(v_e_172_);
v___x_306_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_287_, v___x_288_, v_visitedExpr_295_, v_e_172_);
switch(lean_obj_tag(v___x_306_))
{
case 0:
{
lean_object* v_index_307_; lean_object* v_size_308_; lean_object* v___x_309_; 
v_index_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_index_307_);
lean_dec_ref_known(v___x_306_, 3);
v_size_308_ = lean_ctor_get(v_visitedExpr_295_, 0);
lean_inc(v_size_308_);
lean_inc(v_a_292_);
v___x_309_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedExpr_295_, v_size_308_, v_index_307_, v_e_172_, v_a_292_);
lean_dec(v_index_307_);
v___y_181_ = v_newLocalDeclsForMVars_300_;
v___y_182_ = v_toProcess_305_;
v___y_183_ = v_nextExprIdx_302_;
v___y_184_ = v_levelArgs_298_;
v___y_185_ = v_levelParams_296_;
v___y_186_ = v_exprMVarArgs_303_;
v___y_187_ = v_newLetDecls_301_;
v___y_188_ = v_a_292_;
v___y_189_ = v_nextLevelIdx_297_;
v___y_190_ = v_visitedLevel_294_;
v___y_191_ = v_exprFVarArgs_304_;
v___y_192_ = v_newLocalDecls_299_;
v___y_193_ = v___x_309_;
goto v___jp_180_;
}
case 1:
{
lean_object* v_index_310_; lean_object* v_size_311_; lean_object* v_keyArray_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_index_310_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_index_310_);
lean_dec_ref_known(v___x_306_, 1);
v_size_311_ = lean_ctor_get(v_visitedExpr_295_, 0);
v_keyArray_312_ = lean_ctor_get(v_visitedExpr_295_, 1);
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = lean_nat_add(v_size_311_, v___x_313_);
v___x_315_ = lean_array_get_size(v_keyArray_312_);
v___x_316_ = lean_nat_dec_lt(v___x_314_, v___x_315_);
if (v___x_316_ == 0)
{
lean_dec(v___x_314_);
lean_dec(v_index_310_);
v___y_260_ = v___x_288_;
v___y_261_ = v_newLocalDeclsForMVars_300_;
v___y_262_ = v___x_287_;
v___y_263_ = v_toProcess_305_;
v___y_264_ = v_nextExprIdx_302_;
v___y_265_ = v_visitedExpr_295_;
v___y_266_ = v_levelArgs_298_;
v___y_267_ = v_levelParams_296_;
v___y_268_ = v_exprMVarArgs_303_;
v___y_269_ = v_newLetDecls_301_;
v___y_270_ = v_a_292_;
v___y_271_ = v_nextLevelIdx_297_;
v___y_272_ = v_visitedLevel_294_;
v___y_273_ = v_exprFVarArgs_304_;
v___y_274_ = v_newLocalDecls_299_;
goto v___jp_259_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_317_ = lean_unsigned_to_nat(4u);
v___x_318_ = lean_nat_mul(v___x_314_, v___x_317_);
v___x_319_ = lean_unsigned_to_nat(3u);
v___x_320_ = lean_nat_mul(v___x_315_, v___x_319_);
v___x_321_ = lean_nat_dec_le(v___x_318_, v___x_320_);
lean_dec(v___x_320_);
lean_dec(v___x_318_);
if (v___x_321_ == 0)
{
lean_dec(v___x_314_);
lean_dec(v_index_310_);
v___y_260_ = v___x_288_;
v___y_261_ = v_newLocalDeclsForMVars_300_;
v___y_262_ = v___x_287_;
v___y_263_ = v_toProcess_305_;
v___y_264_ = v_nextExprIdx_302_;
v___y_265_ = v_visitedExpr_295_;
v___y_266_ = v_levelArgs_298_;
v___y_267_ = v_levelParams_296_;
v___y_268_ = v_exprMVarArgs_303_;
v___y_269_ = v_newLetDecls_301_;
v___y_270_ = v_a_292_;
v___y_271_ = v_nextLevelIdx_297_;
v___y_272_ = v_visitedLevel_294_;
v___y_273_ = v_exprFVarArgs_304_;
v___y_274_ = v_newLocalDecls_299_;
goto v___jp_259_;
}
else
{
lean_object* v___x_322_; 
lean_inc(v_a_292_);
v___x_322_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedExpr_295_, v___x_314_, v_index_310_, v_e_172_, v_a_292_);
lean_dec(v_index_310_);
v___y_181_ = v_newLocalDeclsForMVars_300_;
v___y_182_ = v_toProcess_305_;
v___y_183_ = v_nextExprIdx_302_;
v___y_184_ = v_levelArgs_298_;
v___y_185_ = v_levelParams_296_;
v___y_186_ = v_exprMVarArgs_303_;
v___y_187_ = v_newLetDecls_301_;
v___y_188_ = v_a_292_;
v___y_189_ = v_nextLevelIdx_297_;
v___y_190_ = v_visitedLevel_294_;
v___y_191_ = v_exprFVarArgs_304_;
v___y_192_ = v_newLocalDecls_299_;
v___y_193_ = v___x_322_;
goto v___jp_180_;
}
}
}
default: 
{
lean_object* v_size_323_; lean_object* v_keyArray_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_size_323_ = lean_ctor_get(v_visitedExpr_295_, 0);
v_keyArray_324_ = lean_ctor_get(v_visitedExpr_295_, 1);
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_nat_add(v_size_323_, v___x_325_);
v___x_327_ = lean_array_get_size(v_keyArray_324_);
v___x_328_ = lean_nat_dec_lt(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
lean_dec(v___x_326_);
v___x_329_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_287_, v___x_288_, v_visitedExpr_295_);
v___y_217_ = v___x_288_;
v___y_218_ = v_newLocalDeclsForMVars_300_;
v___y_219_ = v___x_287_;
v___y_220_ = v_toProcess_305_;
v___y_221_ = v_nextExprIdx_302_;
v___y_222_ = v_levelParams_296_;
v___y_223_ = v_levelArgs_298_;
v___y_224_ = v_exprMVarArgs_303_;
v___y_225_ = v_newLetDecls_301_;
v___y_226_ = v_a_292_;
v___y_227_ = v_nextLevelIdx_297_;
v___y_228_ = v_visitedLevel_294_;
v___y_229_ = v_exprFVarArgs_304_;
v___y_230_ = v_newLocalDecls_299_;
v___y_231_ = v___x_329_;
goto v___jp_216_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_330_ = lean_unsigned_to_nat(4u);
v___x_331_ = lean_nat_mul(v___x_326_, v___x_330_);
lean_dec(v___x_326_);
v___x_332_ = lean_unsigned_to_nat(3u);
v___x_333_ = lean_nat_mul(v___x_327_, v___x_332_);
v___x_334_ = lean_nat_dec_le(v___x_331_, v___x_333_);
lean_dec(v___x_333_);
lean_dec(v___x_331_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
v___x_335_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_287_, v___x_288_, v_visitedExpr_295_);
v___y_217_ = v___x_288_;
v___y_218_ = v_newLocalDeclsForMVars_300_;
v___y_219_ = v___x_287_;
v___y_220_ = v_toProcess_305_;
v___y_221_ = v_nextExprIdx_302_;
v___y_222_ = v_levelParams_296_;
v___y_223_ = v_levelArgs_298_;
v___y_224_ = v_exprMVarArgs_303_;
v___y_225_ = v_newLetDecls_301_;
v___y_226_ = v_a_292_;
v___y_227_ = v_nextLevelIdx_297_;
v___y_228_ = v_visitedLevel_294_;
v___y_229_ = v_exprFVarArgs_304_;
v___y_230_ = v_newLocalDecls_299_;
v___y_231_ = v___x_335_;
goto v___jp_216_;
}
else
{
v___y_217_ = v___x_288_;
v___y_218_ = v_newLocalDeclsForMVars_300_;
v___y_219_ = v___x_287_;
v___y_220_ = v_toProcess_305_;
v___y_221_ = v_nextExprIdx_302_;
v___y_222_ = v_levelParams_296_;
v___y_223_ = v_levelArgs_298_;
v___y_224_ = v_exprMVarArgs_303_;
v___y_225_ = v_newLetDecls_301_;
v___y_226_ = v_a_292_;
v___y_227_ = v_nextLevelIdx_297_;
v___y_228_ = v_visitedLevel_294_;
v___y_229_ = v_exprFVarArgs_304_;
v___y_230_ = v_newLocalDecls_299_;
v___y_231_ = v_visitedExpr_295_;
goto v___jp_216_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_172_);
return v___x_291_;
}
}
else
{
lean_object* v_val_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec_ref(v_e_172_);
lean_dec_ref(v_f_171_);
v_val_336_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_289_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_val_336_);
lean_dec(v___x_289_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 0);
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_val_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object* v_f_348_, lean_object* v_e_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
uint8_t v_a_boxed_357_; lean_object* v_res_358_; 
v_a_boxed_357_ = lean_unbox(v_a_350_);
v_res_358_ = l_Lean_Meta_Closure_visitExpr(v_f_348_, v_e_349_, v_a_boxed_357_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg(lean_object* v_u_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_nextLevelIdx_367_; lean_object* v_visitedLevel_368_; lean_object* v_visitedExpr_369_; lean_object* v_levelParams_370_; lean_object* v_nextLevelIdx_371_; lean_object* v_levelArgs_372_; lean_object* v_newLocalDecls_373_; lean_object* v_newLocalDeclsForMVars_374_; lean_object* v_newLetDecls_375_; lean_object* v_nextExprIdx_376_; lean_object* v_exprMVarArgs_377_; lean_object* v_exprFVarArgs_378_; lean_object* v_toProcess_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_395_; 
v___x_365_ = lean_st_ref_get(v_a_363_);
v___x_366_ = lean_st_ref_take(v_a_363_);
v_nextLevelIdx_367_ = lean_ctor_get(v___x_365_, 3);
lean_inc(v_nextLevelIdx_367_);
lean_dec(v___x_365_);
v_visitedLevel_368_ = lean_ctor_get(v___x_366_, 0);
v_visitedExpr_369_ = lean_ctor_get(v___x_366_, 1);
v_levelParams_370_ = lean_ctor_get(v___x_366_, 2);
v_nextLevelIdx_371_ = lean_ctor_get(v___x_366_, 3);
v_levelArgs_372_ = lean_ctor_get(v___x_366_, 4);
v_newLocalDecls_373_ = lean_ctor_get(v___x_366_, 5);
v_newLocalDeclsForMVars_374_ = lean_ctor_get(v___x_366_, 6);
v_newLetDecls_375_ = lean_ctor_get(v___x_366_, 7);
v_nextExprIdx_376_ = lean_ctor_get(v___x_366_, 8);
v_exprMVarArgs_377_ = lean_ctor_get(v___x_366_, 9);
v_exprFVarArgs_378_ = lean_ctor_get(v___x_366_, 10);
v_toProcess_379_ = lean_ctor_get(v___x_366_, 11);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_395_ == 0)
{
v___x_381_ = v___x_366_;
v_isShared_382_ = v_isSharedCheck_395_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_toProcess_379_);
lean_inc(v_exprFVarArgs_378_);
lean_inc(v_exprMVarArgs_377_);
lean_inc(v_nextExprIdx_376_);
lean_inc(v_newLetDecls_375_);
lean_inc(v_newLocalDeclsForMVars_374_);
lean_inc(v_newLocalDecls_373_);
lean_inc(v_levelArgs_372_);
lean_inc(v_nextLevelIdx_371_);
lean_inc(v_levelParams_370_);
lean_inc(v_visitedExpr_369_);
lean_inc(v_visitedLevel_368_);
lean_dec(v___x_366_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_395_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_383_ = ((lean_object*)(l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1));
v___x_384_ = lean_name_append_index_after(v___x_383_, v_nextLevelIdx_367_);
lean_inc(v___x_384_);
v___x_385_ = lean_array_push(v_levelParams_370_, v___x_384_);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_nextLevelIdx_371_, v___x_386_);
lean_dec(v_nextLevelIdx_371_);
v___x_388_ = lean_array_push(v_levelArgs_372_, v_u_362_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 4, v___x_388_);
lean_ctor_set(v___x_381_, 3, v___x_387_);
lean_ctor_set(v___x_381_, 2, v___x_385_);
v___x_390_ = v___x_381_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_visitedLevel_368_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_visitedExpr_369_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_394_, 5, v_newLocalDecls_373_);
lean_ctor_set(v_reuseFailAlloc_394_, 6, v_newLocalDeclsForMVars_374_);
lean_ctor_set(v_reuseFailAlloc_394_, 7, v_newLetDecls_375_);
lean_ctor_set(v_reuseFailAlloc_394_, 8, v_nextExprIdx_376_);
lean_ctor_set(v_reuseFailAlloc_394_, 9, v_exprMVarArgs_377_);
lean_ctor_set(v_reuseFailAlloc_394_, 10, v_exprFVarArgs_378_);
lean_ctor_set(v_reuseFailAlloc_394_, 11, v_toProcess_379_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_st_ref_put(v_a_363_, v___x_390_);
v___x_392_ = l_Lean_mkLevelParam(v___x_384_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___boxed(lean_object* v_u_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_396_, v_a_397_);
lean_dec(v_a_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object* v_u_400_, uint8_t v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_400_, v_a_402_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object* v_u_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
uint8_t v_a_boxed_417_; lean_object* v_res_418_; 
v_a_boxed_417_ = lean_unbox(v_a_410_);
v_res_418_ = l_Lean_Meta_Closure_mkNewLevelParam(v_u_409_, v_a_boxed_417_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_collectLevelAux_spec__0(lean_object* v_msg_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_box(0);
v___x_421_ = lean_panic_fn_borrowed(v___x_420_, v_msg_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(lean_object* v_m_422_, lean_object* v_query_423_, lean_object* v_x_424_, lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
lean_object* v_zero_427_; uint8_t v_isZero_428_; 
v_zero_427_ = lean_unsigned_to_nat(0u);
v_isZero_428_ = lean_nat_dec_eq(v_x_425_, v_zero_427_);
if (v_isZero_428_ == 1)
{
lean_dec(v_x_426_);
lean_dec(v_x_425_);
if (lean_obj_tag(v_x_424_) == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_box(2);
return v___x_429_;
}
else
{
lean_object* v_val_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
v_val_430_ = lean_ctor_get(v_x_424_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v_x_424_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_val_430_);
lean_dec(v_x_424_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_val_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
else
{
lean_object* v_keyArray_438_; lean_object* v_valueArray_439_; lean_object* v___x_440_; uint8_t v_isSome_441_; 
v_keyArray_438_ = lean_ctor_get(v_m_422_, 1);
v_valueArray_439_ = lean_ctor_get(v_m_422_, 2);
v___x_440_ = lean_array_fget_borrowed(v_keyArray_438_, v_x_426_);
v_isSome_441_ = lean_noption_is_some(v___x_440_);
if (v_isSome_441_ == 0)
{
lean_dec(v_x_425_);
if (lean_obj_tag(v_x_424_) == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v_x_426_);
return v___x_442_;
}
else
{
lean_object* v_val_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec(v_x_426_);
v_val_443_ = lean_ctor_get(v_x_424_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v_x_424_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_val_443_);
lean_dec(v_x_424_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_val_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_one_451_; lean_object* v_n_452_; lean_object* v___y_454_; 
v_one_451_ = lean_unsigned_to_nat(1u);
v_n_452_ = lean_nat_sub(v_x_425_, v_one_451_);
lean_dec(v_x_425_);
if (v_isSome_441_ == 0)
{
goto v___jp_460_;
}
else
{
lean_object* v___x_462_; uint8_t v_isSome_463_; 
v___x_462_ = lean_array_fget_borrowed(v_valueArray_439_, v_x_426_);
v_isSome_463_ = lean_noption_is_some(v___x_462_);
if (v_isSome_463_ == 0)
{
goto v___jp_460_;
}
else
{
lean_object* v_val_464_; uint8_t v___x_465_; 
lean_inc(v___x_440_);
v_val_464_ = lean_noption_get(v___x_440_);
v___x_465_ = lean_level_eq(v_val_464_, v_query_423_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
lean_dec(v_val_464_);
v___x_466_ = lean_array_get_size(v_keyArray_438_);
v___x_467_ = lean_nat_add(v_x_426_, v_one_451_);
lean_dec(v_x_426_);
v___x_468_ = lean_nat_dec_lt(v___x_467_, v___x_466_);
if (v___x_468_ == 0)
{
lean_dec(v___x_467_);
v_x_425_ = v_n_452_;
v_x_426_ = v_zero_427_;
goto _start;
}
else
{
v_x_425_ = v_n_452_;
v_x_426_ = v___x_467_;
goto _start;
}
}
else
{
lean_object* v_val_471_; lean_object* v___x_472_; 
lean_dec(v_n_452_);
lean_dec(v_x_424_);
lean_inc(v___x_462_);
v_val_471_ = lean_noption_get(v___x_462_);
v___x_472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_472_, 0, v_x_426_);
lean_ctor_set(v___x_472_, 1, v_val_464_);
lean_ctor_set(v___x_472_, 2, v_val_471_);
return v___x_472_;
}
}
}
v___jp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_455_ = lean_array_get_size(v_keyArray_438_);
v___x_456_ = lean_nat_add(v_x_426_, v_one_451_);
lean_dec(v_x_426_);
v___x_457_ = lean_nat_dec_lt(v___x_456_, v___x_455_);
if (v___x_457_ == 0)
{
lean_dec(v___x_456_);
v_x_424_ = v___y_454_;
v_x_425_ = v_n_452_;
v_x_426_ = v_zero_427_;
goto _start;
}
else
{
v_x_424_ = v___y_454_;
v_x_425_ = v_n_452_;
v_x_426_ = v___x_456_;
goto _start;
}
}
v___jp_460_:
{
if (lean_obj_tag(v_x_424_) == 0)
{
lean_object* v___x_461_; 
lean_inc(v_x_426_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v_x_426_);
v___y_454_ = v___x_461_;
goto v___jp_453_;
}
else
{
v___y_454_ = v_x_424_;
goto v___jp_453_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg___boxed(lean_object* v_m_473_, lean_object* v_query_474_, lean_object* v_x_475_, lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_m_473_, v_query_474_, v_x_475_, v_x_476_, v_x_477_);
lean_dec(v_query_474_);
lean_dec_ref(v_m_473_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(lean_object* v_m_479_, lean_object* v_query_480_){
_start:
{
lean_object* v_keyArray_481_; lean_object* v___x_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v_fold_486_; uint64_t v___x_487_; uint64_t v___x_488_; uint64_t v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_keyArray_481_ = lean_ctor_get(v_m_479_, 1);
v___x_482_ = lean_array_get_size(v_keyArray_481_);
v___x_483_ = l_Lean_Level_hash(v_query_480_);
v___x_484_ = 32ULL;
v___x_485_ = lean_uint64_shift_right(v___x_483_, v___x_484_);
v_fold_486_ = lean_uint64_xor(v___x_483_, v___x_485_);
v___x_487_ = 16ULL;
v___x_488_ = lean_uint64_shift_right(v_fold_486_, v___x_487_);
v___x_489_ = lean_uint64_xor(v_fold_486_, v___x_488_);
v___x_490_ = lean_uint64_to_usize(v___x_489_);
v___x_491_ = lean_usize_of_nat(v___x_482_);
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_sub(v___x_491_, v___x_492_);
v___x_494_ = lean_usize_land(v___x_490_, v___x_493_);
v___x_495_ = lean_usize_to_nat(v___x_494_);
v___x_496_ = lean_box(0);
v___x_497_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_m_479_, v_query_480_, v___x_496_, v___x_482_, v___x_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg___boxed(lean_object* v_m_498_, lean_object* v_query_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_m_498_, v_query_499_);
lean_dec(v_query_499_);
lean_dec_ref(v_m_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(lean_object* v_m_501_, lean_object* v_query_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_m_501_, v_query_502_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_index_504_; lean_object* v_key_505_; lean_object* v_value_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_index_504_ = lean_ctor_get(v___x_503_, 0);
v_key_505_ = lean_ctor_get(v___x_503_, 1);
v_value_506_ = lean_ctor_get(v___x_503_, 2);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_503_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_value_506_);
lean_inc(v_key_505_);
lean_inc(v_index_504_);
lean_dec(v___x_503_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_index_504_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_key_505_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_value_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
else
{
lean_object* v___x_514_; 
lean_dec(v___x_503_);
v___x_514_ = lean_box(1);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg___boxed(lean_object* v_m_515_, lean_object* v_query_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_m_515_, v_query_516_);
lean_dec(v_query_516_);
lean_dec_ref(v_m_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(lean_object* v_m_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_m_518_, v_a_519_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_value_521_; lean_object* v___x_522_; 
v_value_521_ = lean_ctor_get(v___x_520_, 2);
lean_inc(v_value_521_);
lean_dec_ref_known(v___x_520_, 3);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v_value_521_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; 
v___x_523_ = lean_box(0);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg___boxed(lean_object* v_m_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_m_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5_spec__6___redArg(lean_object* v_b_527_, lean_object* v_acc_528_, lean_object* v_i_529_){
_start:
{
lean_object* v___y_531_; lean_object* v_keyArray_539_; lean_object* v_valueArray_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_keyArray_539_ = lean_ctor_get(v_b_527_, 1);
v_valueArray_540_ = lean_ctor_get(v_b_527_, 2);
v___x_541_ = lean_array_get_size(v_keyArray_539_);
v___x_542_ = lean_nat_dec_lt(v_i_529_, v___x_541_);
if (v___x_542_ == 0)
{
lean_dec(v_i_529_);
return v_acc_528_;
}
else
{
lean_object* v___x_543_; uint8_t v_isSome_544_; 
v___x_543_ = lean_array_fget_borrowed(v_keyArray_539_, v_i_529_);
v_isSome_544_ = lean_noption_is_some(v___x_543_);
if (v_isSome_544_ == 0)
{
goto v___jp_535_;
}
else
{
lean_object* v___x_545_; uint8_t v_isSome_546_; 
v___x_545_ = lean_array_fget_borrowed(v_valueArray_540_, v_i_529_);
v_isSome_546_ = lean_noption_is_some(v___x_545_);
if (v_isSome_546_ == 0)
{
goto v___jp_535_;
}
else
{
lean_object* v_val_547_; lean_object* v_val_548_; lean_object* v_i_550_; lean_object* v___x_555_; 
lean_inc(v___x_543_);
v_val_547_ = lean_noption_get(v___x_543_);
lean_inc(v___x_545_);
v_val_548_ = lean_noption_get(v___x_545_);
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_acc_528_, v_val_547_);
switch(lean_obj_tag(v___x_555_))
{
case 0:
{
lean_object* v_index_556_; lean_object* v_size_557_; lean_object* v___x_558_; 
v_index_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_index_556_);
lean_dec_ref_known(v___x_555_, 3);
v_size_557_ = lean_ctor_get(v_acc_528_, 0);
lean_inc(v_size_557_);
v___x_558_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_528_, v_size_557_, v_index_556_, v_val_547_, v_val_548_);
lean_dec(v_index_556_);
v___y_531_ = v___x_558_;
goto v___jp_530_;
}
case 1:
{
lean_object* v_index_559_; 
v_index_559_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_index_559_);
lean_dec_ref_known(v___x_555_, 1);
v_i_550_ = v_index_559_;
goto v___jp_549_;
}
default: 
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_528_, v___x_560_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_index_562_; 
v_index_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_index_562_);
lean_dec_ref_known(v___x_561_, 1);
v_i_550_ = v_index_562_;
goto v___jp_549_;
}
else
{
lean_dec(v_val_548_);
lean_dec(v_val_547_);
v___y_531_ = v_acc_528_;
goto v___jp_530_;
}
}
}
v___jp_549_:
{
lean_object* v_size_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_size_551_ = lean_ctor_get(v_acc_528_, 0);
v___x_552_ = lean_unsigned_to_nat(1u);
v___x_553_ = lean_nat_add(v_size_551_, v___x_552_);
v___x_554_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_528_, v___x_553_, v_i_550_, v_val_547_, v_val_548_);
lean_dec(v_i_550_);
v___y_531_ = v___x_554_;
goto v___jp_530_;
}
}
}
}
v___jp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(1u);
v___x_533_ = lean_nat_add(v_i_529_, v___x_532_);
lean_dec(v_i_529_);
v_acc_528_ = v___y_531_;
v_i_529_ = v___x_533_;
goto _start;
}
v___jp_535_:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = lean_nat_add(v_i_529_, v___x_536_);
lean_dec(v_i_529_);
v_i_529_ = v___x_537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_b_563_, lean_object* v_acc_564_, lean_object* v_i_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5_spec__6___redArg(v_b_563_, v_acc_564_, v_i_565_);
lean_dec_ref(v_b_563_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5___redArg(lean_object* v_init_567_, lean_object* v_b_568_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5_spec__6___redArg(v_b_568_, v_init_567_, v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5___redArg___boxed(lean_object* v_init_571_, lean_object* v_b_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5___redArg(v_init_571_, v_b_572_);
lean_dec_ref(v_b_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(lean_object* v_m_574_){
_start:
{
lean_object* v_keyArray_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v_cellCount_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v_target_582_; lean_object* v___x_583_; 
v_keyArray_575_ = lean_ctor_get(v_m_574_, 1);
v___x_576_ = lean_array_get_size(v_keyArray_575_);
v___x_577_ = lean_unsigned_to_nat(2u);
v_cellCount_578_ = lean_nat_mul(v___x_576_, v___x_577_);
v___x_579_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_578_);
v___x_580_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_578_);
v___x_581_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_578_);
v_target_582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_582_, 0, v___x_579_);
lean_ctor_set(v_target_582_, 1, v___x_580_);
lean_ctor_set(v_target_582_, 2, v___x_581_);
v___x_583_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5___redArg(v_target_582_, v_m_574_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg___boxed(lean_object* v_m_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_m_584_);
lean_dec_ref(v_m_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg(lean_object* v_x_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___y_590_; lean_object* v___y_591_; uint8_t v___y_592_; lean_object* v___y_598_; lean_object* v___y_599_; uint8_t v___y_600_; 
switch(lean_obj_tag(v_x_586_))
{
case 0:
{
lean_object* v___x_605_; 
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v_x_586_);
return v___x_605_;
}
case 1:
{
lean_object* v_a_606_; lean_object* v_a_608_; lean_object* v___y_616_; lean_object* v_visitedExpr_617_; lean_object* v_levelParams_618_; lean_object* v_nextLevelIdx_619_; lean_object* v_levelArgs_620_; lean_object* v_newLocalDecls_621_; lean_object* v_newLocalDeclsForMVars_622_; lean_object* v_newLetDecls_623_; lean_object* v_nextExprIdx_624_; lean_object* v_exprMVarArgs_625_; lean_object* v_exprFVarArgs_626_; lean_object* v_toProcess_627_; lean_object* v___y_628_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v_i_650_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v_i_671_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; uint8_t v___x_740_; 
v_a_606_ = lean_ctor_get(v_x_586_, 0);
v___x_740_ = l_Lean_Level_hasMVar(v_a_606_);
if (v___x_740_ == 0)
{
uint8_t v___x_741_; 
v___x_741_ = l_Lean_Level_hasParam(v_a_606_);
if (v___x_741_ == 0)
{
lean_inc(v_a_606_);
v_a_608_ = v_a_606_;
goto v___jp_607_;
}
else
{
goto v___jp_689_;
}
}
else
{
goto v___jp_689_;
}
v___jp_607_:
{
size_t v___x_609_; size_t v___x_610_; uint8_t v___x_611_; 
v___x_609_ = lean_ptr_addr(v_a_606_);
v___x_610_ = lean_ptr_addr(v_a_608_);
v___x_611_ = lean_usize_dec_eq(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec_ref_known(v_x_586_, 1);
v___x_612_ = l_Lean_Level_succ___override(v_a_608_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
else
{
lean_object* v___x_614_; 
lean_dec(v_a_608_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v_x_586_);
return v___x_614_;
}
}
v___jp_615_:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_629_, 0, v___y_628_);
lean_ctor_set(v___x_629_, 1, v_visitedExpr_617_);
lean_ctor_set(v___x_629_, 2, v_levelParams_618_);
lean_ctor_set(v___x_629_, 3, v_nextLevelIdx_619_);
lean_ctor_set(v___x_629_, 4, v_levelArgs_620_);
lean_ctor_set(v___x_629_, 5, v_newLocalDecls_621_);
lean_ctor_set(v___x_629_, 6, v_newLocalDeclsForMVars_622_);
lean_ctor_set(v___x_629_, 7, v_newLetDecls_623_);
lean_ctor_set(v___x_629_, 8, v_nextExprIdx_624_);
lean_ctor_set(v___x_629_, 9, v_exprMVarArgs_625_);
lean_ctor_set(v___x_629_, 10, v_exprFVarArgs_626_);
lean_ctor_set(v___x_629_, 11, v_toProcess_627_);
v___x_630_ = lean_st_ref_put(v_a_587_, v___x_629_);
v_a_608_ = v___y_616_;
goto v___jp_607_;
}
v___jp_631_:
{
lean_object* v_visitedExpr_635_; lean_object* v_levelParams_636_; lean_object* v_nextLevelIdx_637_; lean_object* v_levelArgs_638_; lean_object* v_newLocalDecls_639_; lean_object* v_newLocalDeclsForMVars_640_; lean_object* v_newLetDecls_641_; lean_object* v_nextExprIdx_642_; lean_object* v_exprMVarArgs_643_; lean_object* v_exprFVarArgs_644_; lean_object* v_toProcess_645_; 
v_visitedExpr_635_ = lean_ctor_get(v___y_633_, 1);
lean_inc_ref(v_visitedExpr_635_);
v_levelParams_636_ = lean_ctor_get(v___y_633_, 2);
lean_inc_ref(v_levelParams_636_);
v_nextLevelIdx_637_ = lean_ctor_get(v___y_633_, 3);
lean_inc(v_nextLevelIdx_637_);
v_levelArgs_638_ = lean_ctor_get(v___y_633_, 4);
lean_inc_ref(v_levelArgs_638_);
v_newLocalDecls_639_ = lean_ctor_get(v___y_633_, 5);
lean_inc_ref(v_newLocalDecls_639_);
v_newLocalDeclsForMVars_640_ = lean_ctor_get(v___y_633_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_640_);
v_newLetDecls_641_ = lean_ctor_get(v___y_633_, 7);
lean_inc_ref(v_newLetDecls_641_);
v_nextExprIdx_642_ = lean_ctor_get(v___y_633_, 8);
lean_inc(v_nextExprIdx_642_);
v_exprMVarArgs_643_ = lean_ctor_get(v___y_633_, 9);
lean_inc_ref(v_exprMVarArgs_643_);
v_exprFVarArgs_644_ = lean_ctor_get(v___y_633_, 10);
lean_inc_ref(v_exprFVarArgs_644_);
v_toProcess_645_ = lean_ctor_get(v___y_633_, 11);
lean_inc_ref(v_toProcess_645_);
lean_dec_ref(v___y_633_);
v___y_616_ = v___y_632_;
v_visitedExpr_617_ = v_visitedExpr_635_;
v_levelParams_618_ = v_levelParams_636_;
v_nextLevelIdx_619_ = v_nextLevelIdx_637_;
v_levelArgs_620_ = v_levelArgs_638_;
v_newLocalDecls_621_ = v_newLocalDecls_639_;
v_newLocalDeclsForMVars_622_ = v_newLocalDeclsForMVars_640_;
v_newLetDecls_623_ = v_newLetDecls_641_;
v_nextExprIdx_624_ = v_nextExprIdx_642_;
v_exprMVarArgs_625_ = v_exprMVarArgs_643_;
v_exprFVarArgs_626_ = v_exprFVarArgs_644_;
v_toProcess_627_ = v_toProcess_645_;
v___y_628_ = v___y_634_;
goto v___jp_615_;
}
v___jp_646_:
{
lean_object* v_size_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_size_651_ = lean_ctor_get(v___y_648_, 0);
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_nat_add(v_size_651_, v___x_652_);
lean_inc(v___y_647_);
lean_inc(v_a_606_);
v___x_654_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_648_, v___x_653_, v_i_650_, v_a_606_, v___y_647_);
lean_dec(v_i_650_);
v___y_632_ = v___y_647_;
v___y_633_ = v___y_649_;
v___y_634_ = v___x_654_;
goto v___jp_631_;
}
v___jp_655_:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v___y_658_, v_a_606_);
switch(lean_obj_tag(v___x_659_))
{
case 0:
{
lean_object* v_index_660_; lean_object* v_size_661_; lean_object* v___x_662_; 
v_index_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_index_660_);
lean_dec_ref_known(v___x_659_, 3);
v_size_661_ = lean_ctor_get(v___y_658_, 0);
lean_inc(v_size_661_);
lean_inc(v___y_656_);
lean_inc(v_a_606_);
v___x_662_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_658_, v_size_661_, v_index_660_, v_a_606_, v___y_656_);
lean_dec(v_index_660_);
v___y_632_ = v___y_656_;
v___y_633_ = v___y_657_;
v___y_634_ = v___x_662_;
goto v___jp_631_;
}
case 1:
{
lean_object* v_index_663_; 
v_index_663_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_index_663_);
lean_dec_ref_known(v___x_659_, 1);
v___y_647_ = v___y_656_;
v___y_648_ = v___y_658_;
v___y_649_ = v___y_657_;
v_i_650_ = v_index_663_;
goto v___jp_646_;
}
default: 
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_658_, v___x_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_index_666_; 
v_index_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_index_666_);
lean_dec_ref_known(v___x_665_, 1);
v___y_647_ = v___y_656_;
v___y_648_ = v___y_658_;
v___y_649_ = v___y_657_;
v_i_650_ = v_index_666_;
goto v___jp_646_;
}
else
{
v___y_632_ = v___y_656_;
v___y_633_ = v___y_657_;
v___y_634_ = v___y_658_;
goto v___jp_631_;
}
}
}
}
v___jp_667_:
{
lean_object* v_size_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_size_672_ = lean_ctor_get(v___y_669_, 0);
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v_size_672_, v___x_673_);
lean_inc(v___y_668_);
lean_inc(v_a_606_);
v___x_675_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_669_, v___x_674_, v_i_671_, v_a_606_, v___y_668_);
lean_dec(v_i_671_);
v___y_632_ = v___y_668_;
v___y_633_ = v___y_670_;
v___y_634_ = v___x_675_;
goto v___jp_631_;
}
v___jp_676_:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v___y_677_);
lean_dec_ref(v___y_677_);
v___x_681_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v___x_680_, v_a_606_);
switch(lean_obj_tag(v___x_681_))
{
case 0:
{
lean_object* v_index_682_; lean_object* v_size_683_; lean_object* v___x_684_; 
v_index_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_index_682_);
lean_dec_ref_known(v___x_681_, 3);
v_size_683_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_size_683_);
lean_inc(v___y_678_);
lean_inc(v_a_606_);
v___x_684_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_680_, v_size_683_, v_index_682_, v_a_606_, v___y_678_);
lean_dec(v_index_682_);
v___y_632_ = v___y_678_;
v___y_633_ = v___y_679_;
v___y_634_ = v___x_684_;
goto v___jp_631_;
}
case 1:
{
lean_object* v_index_685_; 
v_index_685_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_index_685_);
lean_dec_ref_known(v___x_681_, 1);
v___y_668_ = v___y_678_;
v___y_669_ = v___x_680_;
v___y_670_ = v___y_679_;
v_i_671_ = v_index_685_;
goto v___jp_667_;
}
default: 
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_680_, v___x_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_index_688_; 
v_index_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_index_688_);
lean_dec_ref_known(v___x_687_, 1);
v___y_668_ = v___y_678_;
v___y_669_ = v___x_680_;
v___y_670_ = v___y_679_;
v_i_671_ = v_index_688_;
goto v___jp_667_;
}
else
{
v___y_632_ = v___y_678_;
v___y_633_ = v___y_679_;
v___y_634_ = v___x_680_;
goto v___jp_631_;
}
}
}
}
v___jp_689_:
{
lean_object* v___x_690_; lean_object* v_visitedLevel_691_; lean_object* v___x_692_; 
v___x_690_ = lean_st_ref_get(v_a_587_);
v_visitedLevel_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref(v_visitedLevel_691_);
lean_dec(v___x_690_);
v___x_692_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_691_, v_a_606_);
lean_dec_ref(v_visitedLevel_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_693_; 
lean_inc(v_a_606_);
v___x_693_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_606_, v_a_587_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v_visitedLevel_696_; lean_object* v_visitedExpr_697_; lean_object* v_levelParams_698_; lean_object* v_nextLevelIdx_699_; lean_object* v_levelArgs_700_; lean_object* v_newLocalDecls_701_; lean_object* v_newLocalDeclsForMVars_702_; lean_object* v_newLetDecls_703_; lean_object* v_nextExprIdx_704_; lean_object* v_exprMVarArgs_705_; lean_object* v_exprFVarArgs_706_; lean_object* v_toProcess_707_; lean_object* v___x_708_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = lean_st_ref_take(v_a_587_);
v_visitedLevel_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_visitedLevel_696_);
v_visitedExpr_697_ = lean_ctor_get(v___x_695_, 1);
lean_inc_ref(v_visitedExpr_697_);
v_levelParams_698_ = lean_ctor_get(v___x_695_, 2);
lean_inc_ref(v_levelParams_698_);
v_nextLevelIdx_699_ = lean_ctor_get(v___x_695_, 3);
lean_inc(v_nextLevelIdx_699_);
v_levelArgs_700_ = lean_ctor_get(v___x_695_, 4);
lean_inc_ref(v_levelArgs_700_);
v_newLocalDecls_701_ = lean_ctor_get(v___x_695_, 5);
lean_inc_ref(v_newLocalDecls_701_);
v_newLocalDeclsForMVars_702_ = lean_ctor_get(v___x_695_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_702_);
v_newLetDecls_703_ = lean_ctor_get(v___x_695_, 7);
lean_inc_ref(v_newLetDecls_703_);
v_nextExprIdx_704_ = lean_ctor_get(v___x_695_, 8);
lean_inc(v_nextExprIdx_704_);
v_exprMVarArgs_705_ = lean_ctor_get(v___x_695_, 9);
lean_inc_ref(v_exprMVarArgs_705_);
v_exprFVarArgs_706_ = lean_ctor_get(v___x_695_, 10);
lean_inc_ref(v_exprFVarArgs_706_);
v_toProcess_707_ = lean_ctor_get(v___x_695_, 11);
lean_inc_ref(v_toProcess_707_);
v___x_708_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_696_, v_a_606_);
switch(lean_obj_tag(v___x_708_))
{
case 0:
{
lean_object* v_index_709_; lean_object* v_size_710_; lean_object* v___x_711_; 
lean_dec(v___x_695_);
v_index_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_index_709_);
lean_dec_ref_known(v___x_708_, 3);
v_size_710_ = lean_ctor_get(v_visitedLevel_696_, 0);
lean_inc(v_size_710_);
lean_inc(v_a_694_);
lean_inc(v_a_606_);
v___x_711_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_696_, v_size_710_, v_index_709_, v_a_606_, v_a_694_);
lean_dec(v_index_709_);
v___y_616_ = v_a_694_;
v_visitedExpr_617_ = v_visitedExpr_697_;
v_levelParams_618_ = v_levelParams_698_;
v_nextLevelIdx_619_ = v_nextLevelIdx_699_;
v_levelArgs_620_ = v_levelArgs_700_;
v_newLocalDecls_621_ = v_newLocalDecls_701_;
v_newLocalDeclsForMVars_622_ = v_newLocalDeclsForMVars_702_;
v_newLetDecls_623_ = v_newLetDecls_703_;
v_nextExprIdx_624_ = v_nextExprIdx_704_;
v_exprMVarArgs_625_ = v_exprMVarArgs_705_;
v_exprFVarArgs_626_ = v_exprFVarArgs_706_;
v_toProcess_627_ = v_toProcess_707_;
v___y_628_ = v___x_711_;
goto v___jp_615_;
}
case 1:
{
lean_object* v_index_712_; lean_object* v_size_713_; lean_object* v_keyArray_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v_index_712_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_index_712_);
lean_dec_ref_known(v___x_708_, 1);
v_size_713_ = lean_ctor_get(v_visitedLevel_696_, 0);
v_keyArray_714_ = lean_ctor_get(v_visitedLevel_696_, 1);
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = lean_nat_add(v_size_713_, v___x_715_);
v___x_717_ = lean_array_get_size(v_keyArray_714_);
v___x_718_ = lean_nat_dec_lt(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_dec(v___x_716_);
lean_dec(v_index_712_);
lean_dec_ref(v_toProcess_707_);
lean_dec_ref(v_exprFVarArgs_706_);
lean_dec_ref(v_exprMVarArgs_705_);
lean_dec(v_nextExprIdx_704_);
lean_dec_ref(v_newLetDecls_703_);
lean_dec_ref(v_newLocalDeclsForMVars_702_);
lean_dec_ref(v_newLocalDecls_701_);
lean_dec_ref(v_levelArgs_700_);
lean_dec(v_nextLevelIdx_699_);
lean_dec_ref(v_levelParams_698_);
lean_dec_ref(v_visitedExpr_697_);
v___y_677_ = v_visitedLevel_696_;
v___y_678_ = v_a_694_;
v___y_679_ = v___x_695_;
goto v___jp_676_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_719_ = lean_unsigned_to_nat(4u);
v___x_720_ = lean_nat_mul(v___x_716_, v___x_719_);
v___x_721_ = lean_unsigned_to_nat(3u);
v___x_722_ = lean_nat_mul(v___x_717_, v___x_721_);
v___x_723_ = lean_nat_dec_le(v___x_720_, v___x_722_);
lean_dec(v___x_722_);
lean_dec(v___x_720_);
if (v___x_723_ == 0)
{
lean_dec(v___x_716_);
lean_dec(v_index_712_);
lean_dec_ref(v_toProcess_707_);
lean_dec_ref(v_exprFVarArgs_706_);
lean_dec_ref(v_exprMVarArgs_705_);
lean_dec(v_nextExprIdx_704_);
lean_dec_ref(v_newLetDecls_703_);
lean_dec_ref(v_newLocalDeclsForMVars_702_);
lean_dec_ref(v_newLocalDecls_701_);
lean_dec_ref(v_levelArgs_700_);
lean_dec(v_nextLevelIdx_699_);
lean_dec_ref(v_levelParams_698_);
lean_dec_ref(v_visitedExpr_697_);
v___y_677_ = v_visitedLevel_696_;
v___y_678_ = v_a_694_;
v___y_679_ = v___x_695_;
goto v___jp_676_;
}
else
{
lean_object* v___x_724_; 
lean_dec(v___x_695_);
lean_inc(v_a_694_);
lean_inc(v_a_606_);
v___x_724_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_696_, v___x_716_, v_index_712_, v_a_606_, v_a_694_);
lean_dec(v_index_712_);
v___y_616_ = v_a_694_;
v_visitedExpr_617_ = v_visitedExpr_697_;
v_levelParams_618_ = v_levelParams_698_;
v_nextLevelIdx_619_ = v_nextLevelIdx_699_;
v_levelArgs_620_ = v_levelArgs_700_;
v_newLocalDecls_621_ = v_newLocalDecls_701_;
v_newLocalDeclsForMVars_622_ = v_newLocalDeclsForMVars_702_;
v_newLetDecls_623_ = v_newLetDecls_703_;
v_nextExprIdx_624_ = v_nextExprIdx_704_;
v_exprMVarArgs_625_ = v_exprMVarArgs_705_;
v_exprFVarArgs_626_ = v_exprFVarArgs_706_;
v_toProcess_627_ = v_toProcess_707_;
v___y_628_ = v___x_724_;
goto v___jp_615_;
}
}
}
default: 
{
lean_object* v_size_725_; lean_object* v_keyArray_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
lean_dec_ref(v_toProcess_707_);
lean_dec_ref(v_exprFVarArgs_706_);
lean_dec_ref(v_exprMVarArgs_705_);
lean_dec(v_nextExprIdx_704_);
lean_dec_ref(v_newLetDecls_703_);
lean_dec_ref(v_newLocalDeclsForMVars_702_);
lean_dec_ref(v_newLocalDecls_701_);
lean_dec_ref(v_levelArgs_700_);
lean_dec(v_nextLevelIdx_699_);
lean_dec_ref(v_levelParams_698_);
lean_dec_ref(v_visitedExpr_697_);
v_size_725_ = lean_ctor_get(v_visitedLevel_696_, 0);
v_keyArray_726_ = lean_ctor_get(v_visitedLevel_696_, 1);
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_add(v_size_725_, v___x_727_);
v___x_729_ = lean_array_get_size(v_keyArray_726_);
v___x_730_ = lean_nat_dec_lt(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
lean_dec(v___x_728_);
v___x_731_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_visitedLevel_696_);
lean_dec_ref(v_visitedLevel_696_);
v___y_656_ = v_a_694_;
v___y_657_ = v___x_695_;
v___y_658_ = v___x_731_;
goto v___jp_655_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_732_ = lean_unsigned_to_nat(4u);
v___x_733_ = lean_nat_mul(v___x_728_, v___x_732_);
lean_dec(v___x_728_);
v___x_734_ = lean_unsigned_to_nat(3u);
v___x_735_ = lean_nat_mul(v___x_729_, v___x_734_);
v___x_736_ = lean_nat_dec_le(v___x_733_, v___x_735_);
lean_dec(v___x_735_);
lean_dec(v___x_733_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
v___x_737_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_visitedLevel_696_);
lean_dec_ref(v_visitedLevel_696_);
v___y_656_ = v_a_694_;
v___y_657_ = v___x_695_;
v___y_658_ = v___x_737_;
goto v___jp_655_;
}
else
{
v___y_656_ = v_a_694_;
v___y_657_ = v___x_695_;
v___y_658_ = v_visitedLevel_696_;
goto v___jp_655_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_738_; 
v_a_738_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_693_, 1);
v_a_608_ = v_a_738_;
goto v___jp_607_;
}
else
{
lean_dec_ref_known(v_x_586_, 1);
return v___x_693_;
}
}
}
else
{
lean_object* v_val_739_; 
v_val_739_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v___x_692_, 1);
v_a_608_ = v_val_739_;
goto v___jp_607_;
}
}
}
case 2:
{
lean_object* v_a_742_; lean_object* v_a_743_; lean_object* v___y_745_; lean_object* v_a_746_; lean_object* v_visitedExpr_754_; lean_object* v_levelParams_755_; lean_object* v_nextLevelIdx_756_; lean_object* v_levelArgs_757_; lean_object* v_newLocalDecls_758_; lean_object* v_newLocalDeclsForMVars_759_; lean_object* v_newLetDecls_760_; lean_object* v_nextExprIdx_761_; lean_object* v_exprMVarArgs_762_; lean_object* v_exprFVarArgs_763_; lean_object* v_toProcess_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v_i_791_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v_i_814_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_834_; lean_object* v_a_886_; lean_object* v_visitedExpr_890_; lean_object* v_levelParams_891_; lean_object* v_nextLevelIdx_892_; lean_object* v_levelArgs_893_; lean_object* v_newLocalDecls_894_; lean_object* v_newLocalDeclsForMVars_895_; lean_object* v_newLetDecls_896_; lean_object* v_nextExprIdx_897_; lean_object* v_exprMVarArgs_898_; lean_object* v_exprFVarArgs_899_; lean_object* v_toProcess_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v_i_924_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v_i_945_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; uint8_t v___x_1014_; 
v_a_742_ = lean_ctor_get(v_x_586_, 0);
v_a_743_ = lean_ctor_get(v_x_586_, 1);
v___x_1014_ = l_Lean_Level_hasMVar(v_a_742_);
if (v___x_1014_ == 0)
{
uint8_t v___x_1015_; 
v___x_1015_ = l_Lean_Level_hasParam(v_a_742_);
if (v___x_1015_ == 0)
{
lean_inc(v_a_742_);
v_a_886_ = v_a_742_;
goto v___jp_885_;
}
else
{
goto v___jp_963_;
}
}
else
{
goto v___jp_963_;
}
v___jp_744_:
{
size_t v___x_747_; size_t v___x_748_; uint8_t v___x_749_; 
v___x_747_ = lean_ptr_addr(v_a_742_);
v___x_748_ = lean_ptr_addr(v___y_745_);
v___x_749_ = lean_usize_dec_eq(v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
v___y_590_ = v___y_745_;
v___y_591_ = v_a_746_;
v___y_592_ = v___x_749_;
goto v___jp_589_;
}
else
{
size_t v___x_750_; size_t v___x_751_; uint8_t v___x_752_; 
v___x_750_ = lean_ptr_addr(v_a_743_);
v___x_751_ = lean_ptr_addr(v_a_746_);
v___x_752_ = lean_usize_dec_eq(v___x_750_, v___x_751_);
v___y_590_ = v___y_745_;
v___y_591_ = v_a_746_;
v___y_592_ = v___x_752_;
goto v___jp_589_;
}
}
v___jp_753_:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_768_, 0, v___y_767_);
lean_ctor_set(v___x_768_, 1, v_visitedExpr_754_);
lean_ctor_set(v___x_768_, 2, v_levelParams_755_);
lean_ctor_set(v___x_768_, 3, v_nextLevelIdx_756_);
lean_ctor_set(v___x_768_, 4, v_levelArgs_757_);
lean_ctor_set(v___x_768_, 5, v_newLocalDecls_758_);
lean_ctor_set(v___x_768_, 6, v_newLocalDeclsForMVars_759_);
lean_ctor_set(v___x_768_, 7, v_newLetDecls_760_);
lean_ctor_set(v___x_768_, 8, v_nextExprIdx_761_);
lean_ctor_set(v___x_768_, 9, v_exprMVarArgs_762_);
lean_ctor_set(v___x_768_, 10, v_exprFVarArgs_763_);
lean_ctor_set(v___x_768_, 11, v_toProcess_764_);
v___x_769_ = lean_st_ref_put(v_a_587_, v___x_768_);
v___y_745_ = v___y_765_;
v_a_746_ = v___y_766_;
goto v___jp_744_;
}
v___jp_770_:
{
lean_object* v_visitedExpr_775_; lean_object* v_levelParams_776_; lean_object* v_nextLevelIdx_777_; lean_object* v_levelArgs_778_; lean_object* v_newLocalDecls_779_; lean_object* v_newLocalDeclsForMVars_780_; lean_object* v_newLetDecls_781_; lean_object* v_nextExprIdx_782_; lean_object* v_exprMVarArgs_783_; lean_object* v_exprFVarArgs_784_; lean_object* v_toProcess_785_; 
v_visitedExpr_775_ = lean_ctor_get(v___y_771_, 1);
lean_inc_ref(v_visitedExpr_775_);
v_levelParams_776_ = lean_ctor_get(v___y_771_, 2);
lean_inc_ref(v_levelParams_776_);
v_nextLevelIdx_777_ = lean_ctor_get(v___y_771_, 3);
lean_inc(v_nextLevelIdx_777_);
v_levelArgs_778_ = lean_ctor_get(v___y_771_, 4);
lean_inc_ref(v_levelArgs_778_);
v_newLocalDecls_779_ = lean_ctor_get(v___y_771_, 5);
lean_inc_ref(v_newLocalDecls_779_);
v_newLocalDeclsForMVars_780_ = lean_ctor_get(v___y_771_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_780_);
v_newLetDecls_781_ = lean_ctor_get(v___y_771_, 7);
lean_inc_ref(v_newLetDecls_781_);
v_nextExprIdx_782_ = lean_ctor_get(v___y_771_, 8);
lean_inc(v_nextExprIdx_782_);
v_exprMVarArgs_783_ = lean_ctor_get(v___y_771_, 9);
lean_inc_ref(v_exprMVarArgs_783_);
v_exprFVarArgs_784_ = lean_ctor_get(v___y_771_, 10);
lean_inc_ref(v_exprFVarArgs_784_);
v_toProcess_785_ = lean_ctor_get(v___y_771_, 11);
lean_inc_ref(v_toProcess_785_);
lean_dec_ref(v___y_771_);
v_visitedExpr_754_ = v_visitedExpr_775_;
v_levelParams_755_ = v_levelParams_776_;
v_nextLevelIdx_756_ = v_nextLevelIdx_777_;
v_levelArgs_757_ = v_levelArgs_778_;
v_newLocalDecls_758_ = v_newLocalDecls_779_;
v_newLocalDeclsForMVars_759_ = v_newLocalDeclsForMVars_780_;
v_newLetDecls_760_ = v_newLetDecls_781_;
v_nextExprIdx_761_ = v_nextExprIdx_782_;
v_exprMVarArgs_762_ = v_exprMVarArgs_783_;
v_exprFVarArgs_763_ = v_exprFVarArgs_784_;
v_toProcess_764_ = v_toProcess_785_;
v___y_765_ = v___y_772_;
v___y_766_ = v___y_773_;
v___y_767_ = v___y_774_;
goto v___jp_753_;
}
v___jp_786_:
{
lean_object* v_size_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_size_792_ = lean_ctor_get(v___y_790_, 0);
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = lean_nat_add(v_size_792_, v___x_793_);
lean_inc(v___y_789_);
lean_inc(v_a_743_);
v___x_795_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_790_, v___x_794_, v_i_791_, v_a_743_, v___y_789_);
lean_dec(v_i_791_);
v___y_771_ = v___y_787_;
v___y_772_ = v___y_788_;
v___y_773_ = v___y_789_;
v___y_774_ = v___x_795_;
goto v___jp_770_;
}
v___jp_796_:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v___y_800_, v_a_743_);
switch(lean_obj_tag(v___x_801_))
{
case 0:
{
lean_object* v_index_802_; lean_object* v_size_803_; lean_object* v___x_804_; 
v_index_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_index_802_);
lean_dec_ref_known(v___x_801_, 3);
v_size_803_ = lean_ctor_get(v___y_800_, 0);
lean_inc(v_size_803_);
lean_inc(v___y_799_);
lean_inc(v_a_743_);
v___x_804_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_800_, v_size_803_, v_index_802_, v_a_743_, v___y_799_);
lean_dec(v_index_802_);
v___y_771_ = v___y_797_;
v___y_772_ = v___y_798_;
v___y_773_ = v___y_799_;
v___y_774_ = v___x_804_;
goto v___jp_770_;
}
case 1:
{
lean_object* v_index_805_; 
v_index_805_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_index_805_);
lean_dec_ref_known(v___x_801_, 1);
v___y_787_ = v___y_797_;
v___y_788_ = v___y_798_;
v___y_789_ = v___y_799_;
v___y_790_ = v___y_800_;
v_i_791_ = v_index_805_;
goto v___jp_786_;
}
default: 
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_800_, v___x_806_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_index_808_; 
v_index_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_index_808_);
lean_dec_ref_known(v___x_807_, 1);
v___y_787_ = v___y_797_;
v___y_788_ = v___y_798_;
v___y_789_ = v___y_799_;
v___y_790_ = v___y_800_;
v_i_791_ = v_index_808_;
goto v___jp_786_;
}
else
{
v___y_771_ = v___y_797_;
v___y_772_ = v___y_798_;
v___y_773_ = v___y_799_;
v___y_774_ = v___y_800_;
goto v___jp_770_;
}
}
}
}
v___jp_809_:
{
lean_object* v_size_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_size_815_ = lean_ctor_get(v___y_811_, 0);
v___x_816_ = lean_unsigned_to_nat(1u);
v___x_817_ = lean_nat_add(v_size_815_, v___x_816_);
lean_inc(v___y_813_);
lean_inc(v_a_743_);
v___x_818_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_811_, v___x_817_, v_i_814_, v_a_743_, v___y_813_);
lean_dec(v_i_814_);
v___y_771_ = v___y_810_;
v___y_772_ = v___y_812_;
v___y_773_ = v___y_813_;
v___y_774_ = v___x_818_;
goto v___jp_770_;
}
v___jp_819_:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v___y_821_);
lean_dec_ref(v___y_821_);
v___x_825_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v___x_824_, v_a_743_);
switch(lean_obj_tag(v___x_825_))
{
case 0:
{
lean_object* v_index_826_; lean_object* v_size_827_; lean_object* v___x_828_; 
v_index_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_index_826_);
lean_dec_ref_known(v___x_825_, 3);
v_size_827_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_size_827_);
lean_inc(v___y_823_);
lean_inc(v_a_743_);
v___x_828_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_824_, v_size_827_, v_index_826_, v_a_743_, v___y_823_);
lean_dec(v_index_826_);
v___y_771_ = v___y_820_;
v___y_772_ = v___y_822_;
v___y_773_ = v___y_823_;
v___y_774_ = v___x_828_;
goto v___jp_770_;
}
case 1:
{
lean_object* v_index_829_; 
v_index_829_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_index_829_);
lean_dec_ref_known(v___x_825_, 1);
v___y_810_ = v___y_820_;
v___y_811_ = v___x_824_;
v___y_812_ = v___y_822_;
v___y_813_ = v___y_823_;
v_i_814_ = v_index_829_;
goto v___jp_809_;
}
default: 
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_824_, v___x_830_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_index_832_; 
v_index_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_index_832_);
lean_dec_ref_known(v___x_831_, 1);
v___y_810_ = v___y_820_;
v___y_811_ = v___x_824_;
v___y_812_ = v___y_822_;
v___y_813_ = v___y_823_;
v_i_814_ = v_index_832_;
goto v___jp_809_;
}
else
{
v___y_771_ = v___y_820_;
v___y_772_ = v___y_822_;
v___y_773_ = v___y_823_;
v___y_774_ = v___x_824_;
goto v___jp_770_;
}
}
}
}
v___jp_833_:
{
lean_object* v___x_835_; lean_object* v_visitedLevel_836_; lean_object* v___x_837_; 
v___x_835_ = lean_st_ref_get(v_a_587_);
v_visitedLevel_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc_ref(v_visitedLevel_836_);
lean_dec(v___x_835_);
v___x_837_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_836_, v_a_743_);
lean_dec_ref(v_visitedLevel_836_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v___x_838_; 
lean_inc(v_a_743_);
v___x_838_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_743_, v_a_587_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_840_; lean_object* v_visitedLevel_841_; lean_object* v_visitedExpr_842_; lean_object* v_levelParams_843_; lean_object* v_nextLevelIdx_844_; lean_object* v_levelArgs_845_; lean_object* v_newLocalDecls_846_; lean_object* v_newLocalDeclsForMVars_847_; lean_object* v_newLetDecls_848_; lean_object* v_nextExprIdx_849_; lean_object* v_exprMVarArgs_850_; lean_object* v_exprFVarArgs_851_; lean_object* v_toProcess_852_; lean_object* v___x_853_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_838_, 1);
v___x_840_ = lean_st_ref_take(v_a_587_);
v_visitedLevel_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc_ref(v_visitedLevel_841_);
v_visitedExpr_842_ = lean_ctor_get(v___x_840_, 1);
lean_inc_ref(v_visitedExpr_842_);
v_levelParams_843_ = lean_ctor_get(v___x_840_, 2);
lean_inc_ref(v_levelParams_843_);
v_nextLevelIdx_844_ = lean_ctor_get(v___x_840_, 3);
lean_inc(v_nextLevelIdx_844_);
v_levelArgs_845_ = lean_ctor_get(v___x_840_, 4);
lean_inc_ref(v_levelArgs_845_);
v_newLocalDecls_846_ = lean_ctor_get(v___x_840_, 5);
lean_inc_ref(v_newLocalDecls_846_);
v_newLocalDeclsForMVars_847_ = lean_ctor_get(v___x_840_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_847_);
v_newLetDecls_848_ = lean_ctor_get(v___x_840_, 7);
lean_inc_ref(v_newLetDecls_848_);
v_nextExprIdx_849_ = lean_ctor_get(v___x_840_, 8);
lean_inc(v_nextExprIdx_849_);
v_exprMVarArgs_850_ = lean_ctor_get(v___x_840_, 9);
lean_inc_ref(v_exprMVarArgs_850_);
v_exprFVarArgs_851_ = lean_ctor_get(v___x_840_, 10);
lean_inc_ref(v_exprFVarArgs_851_);
v_toProcess_852_ = lean_ctor_get(v___x_840_, 11);
lean_inc_ref(v_toProcess_852_);
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_841_, v_a_743_);
switch(lean_obj_tag(v___x_853_))
{
case 0:
{
lean_object* v_index_854_; lean_object* v_size_855_; lean_object* v___x_856_; 
lean_dec(v___x_840_);
v_index_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_index_854_);
lean_dec_ref_known(v___x_853_, 3);
v_size_855_ = lean_ctor_get(v_visitedLevel_841_, 0);
lean_inc(v_size_855_);
lean_inc(v_a_839_);
lean_inc(v_a_743_);
v___x_856_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_841_, v_size_855_, v_index_854_, v_a_743_, v_a_839_);
lean_dec(v_index_854_);
v_visitedExpr_754_ = v_visitedExpr_842_;
v_levelParams_755_ = v_levelParams_843_;
v_nextLevelIdx_756_ = v_nextLevelIdx_844_;
v_levelArgs_757_ = v_levelArgs_845_;
v_newLocalDecls_758_ = v_newLocalDecls_846_;
v_newLocalDeclsForMVars_759_ = v_newLocalDeclsForMVars_847_;
v_newLetDecls_760_ = v_newLetDecls_848_;
v_nextExprIdx_761_ = v_nextExprIdx_849_;
v_exprMVarArgs_762_ = v_exprMVarArgs_850_;
v_exprFVarArgs_763_ = v_exprFVarArgs_851_;
v_toProcess_764_ = v_toProcess_852_;
v___y_765_ = v___y_834_;
v___y_766_ = v_a_839_;
v___y_767_ = v___x_856_;
goto v___jp_753_;
}
case 1:
{
lean_object* v_index_857_; lean_object* v_size_858_; lean_object* v_keyArray_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_index_857_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_index_857_);
lean_dec_ref_known(v___x_853_, 1);
v_size_858_ = lean_ctor_get(v_visitedLevel_841_, 0);
v_keyArray_859_ = lean_ctor_get(v_visitedLevel_841_, 1);
v___x_860_ = lean_unsigned_to_nat(1u);
v___x_861_ = lean_nat_add(v_size_858_, v___x_860_);
v___x_862_ = lean_array_get_size(v_keyArray_859_);
v___x_863_ = lean_nat_dec_lt(v___x_861_, v___x_862_);
if (v___x_863_ == 0)
{
lean_dec(v___x_861_);
lean_dec(v_index_857_);
lean_dec_ref(v_toProcess_852_);
lean_dec_ref(v_exprFVarArgs_851_);
lean_dec_ref(v_exprMVarArgs_850_);
lean_dec(v_nextExprIdx_849_);
lean_dec_ref(v_newLetDecls_848_);
lean_dec_ref(v_newLocalDeclsForMVars_847_);
lean_dec_ref(v_newLocalDecls_846_);
lean_dec_ref(v_levelArgs_845_);
lean_dec(v_nextLevelIdx_844_);
lean_dec_ref(v_levelParams_843_);
lean_dec_ref(v_visitedExpr_842_);
v___y_820_ = v___x_840_;
v___y_821_ = v_visitedLevel_841_;
v___y_822_ = v___y_834_;
v___y_823_ = v_a_839_;
goto v___jp_819_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_864_ = lean_unsigned_to_nat(4u);
v___x_865_ = lean_nat_mul(v___x_861_, v___x_864_);
v___x_866_ = lean_unsigned_to_nat(3u);
v___x_867_ = lean_nat_mul(v___x_862_, v___x_866_);
v___x_868_ = lean_nat_dec_le(v___x_865_, v___x_867_);
lean_dec(v___x_867_);
lean_dec(v___x_865_);
if (v___x_868_ == 0)
{
lean_dec(v___x_861_);
lean_dec(v_index_857_);
lean_dec_ref(v_toProcess_852_);
lean_dec_ref(v_exprFVarArgs_851_);
lean_dec_ref(v_exprMVarArgs_850_);
lean_dec(v_nextExprIdx_849_);
lean_dec_ref(v_newLetDecls_848_);
lean_dec_ref(v_newLocalDeclsForMVars_847_);
lean_dec_ref(v_newLocalDecls_846_);
lean_dec_ref(v_levelArgs_845_);
lean_dec(v_nextLevelIdx_844_);
lean_dec_ref(v_levelParams_843_);
lean_dec_ref(v_visitedExpr_842_);
v___y_820_ = v___x_840_;
v___y_821_ = v_visitedLevel_841_;
v___y_822_ = v___y_834_;
v___y_823_ = v_a_839_;
goto v___jp_819_;
}
else
{
lean_object* v___x_869_; 
lean_dec(v___x_840_);
lean_inc(v_a_839_);
lean_inc(v_a_743_);
v___x_869_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_841_, v___x_861_, v_index_857_, v_a_743_, v_a_839_);
lean_dec(v_index_857_);
v_visitedExpr_754_ = v_visitedExpr_842_;
v_levelParams_755_ = v_levelParams_843_;
v_nextLevelIdx_756_ = v_nextLevelIdx_844_;
v_levelArgs_757_ = v_levelArgs_845_;
v_newLocalDecls_758_ = v_newLocalDecls_846_;
v_newLocalDeclsForMVars_759_ = v_newLocalDeclsForMVars_847_;
v_newLetDecls_760_ = v_newLetDecls_848_;
v_nextExprIdx_761_ = v_nextExprIdx_849_;
v_exprMVarArgs_762_ = v_exprMVarArgs_850_;
v_exprFVarArgs_763_ = v_exprFVarArgs_851_;
v_toProcess_764_ = v_toProcess_852_;
v___y_765_ = v___y_834_;
v___y_766_ = v_a_839_;
v___y_767_ = v___x_869_;
goto v___jp_753_;
}
}
}
default: 
{
lean_object* v_size_870_; lean_object* v_keyArray_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
lean_dec_ref(v_toProcess_852_);
lean_dec_ref(v_exprFVarArgs_851_);
lean_dec_ref(v_exprMVarArgs_850_);
lean_dec(v_nextExprIdx_849_);
lean_dec_ref(v_newLetDecls_848_);
lean_dec_ref(v_newLocalDeclsForMVars_847_);
lean_dec_ref(v_newLocalDecls_846_);
lean_dec_ref(v_levelArgs_845_);
lean_dec(v_nextLevelIdx_844_);
lean_dec_ref(v_levelParams_843_);
lean_dec_ref(v_visitedExpr_842_);
v_size_870_ = lean_ctor_get(v_visitedLevel_841_, 0);
v_keyArray_871_ = lean_ctor_get(v_visitedLevel_841_, 1);
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_nat_add(v_size_870_, v___x_872_);
v___x_874_ = lean_array_get_size(v_keyArray_871_);
v___x_875_ = lean_nat_dec_lt(v___x_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_dec(v___x_873_);
v___x_876_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_visitedLevel_841_);
lean_dec_ref(v_visitedLevel_841_);
v___y_797_ = v___x_840_;
v___y_798_ = v___y_834_;
v___y_799_ = v_a_839_;
v___y_800_ = v___x_876_;
goto v___jp_796_;
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_877_ = lean_unsigned_to_nat(4u);
v___x_878_ = lean_nat_mul(v___x_873_, v___x_877_);
lean_dec(v___x_873_);
v___x_879_ = lean_unsigned_to_nat(3u);
v___x_880_ = lean_nat_mul(v___x_874_, v___x_879_);
v___x_881_ = lean_nat_dec_le(v___x_878_, v___x_880_);
lean_dec(v___x_880_);
lean_dec(v___x_878_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_visitedLevel_841_);
lean_dec_ref(v_visitedLevel_841_);
v___y_797_ = v___x_840_;
v___y_798_ = v___y_834_;
v___y_799_ = v_a_839_;
v___y_800_ = v___x_882_;
goto v___jp_796_;
}
else
{
v___y_797_ = v___x_840_;
v___y_798_ = v___y_834_;
v___y_799_ = v_a_839_;
v___y_800_ = v_visitedLevel_841_;
goto v___jp_796_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_883_; 
v_a_883_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_838_, 1);
v___y_745_ = v___y_834_;
v_a_746_ = v_a_883_;
goto v___jp_744_;
}
else
{
lean_dec(v___y_834_);
lean_dec_ref_known(v_x_586_, 2);
return v___x_838_;
}
}
}
else
{
lean_object* v_val_884_; 
v_val_884_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v___x_837_, 1);
v___y_745_ = v___y_834_;
v_a_746_ = v_val_884_;
goto v___jp_744_;
}
}
v___jp_885_:
{
uint8_t v___x_887_; 
v___x_887_ = l_Lean_Level_hasMVar(v_a_743_);
if (v___x_887_ == 0)
{
uint8_t v___x_888_; 
v___x_888_ = l_Lean_Level_hasParam(v_a_743_);
if (v___x_888_ == 0)
{
lean_inc(v_a_743_);
v___y_745_ = v_a_886_;
v_a_746_ = v_a_743_;
goto v___jp_744_;
}
else
{
v___y_834_ = v_a_886_;
goto v___jp_833_;
}
}
else
{
v___y_834_ = v_a_886_;
goto v___jp_833_;
}
}
v___jp_889_:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_903_, 0, v___y_902_);
lean_ctor_set(v___x_903_, 1, v_visitedExpr_890_);
lean_ctor_set(v___x_903_, 2, v_levelParams_891_);
lean_ctor_set(v___x_903_, 3, v_nextLevelIdx_892_);
lean_ctor_set(v___x_903_, 4, v_levelArgs_893_);
lean_ctor_set(v___x_903_, 5, v_newLocalDecls_894_);
lean_ctor_set(v___x_903_, 6, v_newLocalDeclsForMVars_895_);
lean_ctor_set(v___x_903_, 7, v_newLetDecls_896_);
lean_ctor_set(v___x_903_, 8, v_nextExprIdx_897_);
lean_ctor_set(v___x_903_, 9, v_exprMVarArgs_898_);
lean_ctor_set(v___x_903_, 10, v_exprFVarArgs_899_);
lean_ctor_set(v___x_903_, 11, v_toProcess_900_);
v___x_904_ = lean_st_ref_put(v_a_587_, v___x_903_);
v_a_886_ = v___y_901_;
goto v___jp_885_;
}
v___jp_905_:
{
lean_object* v_visitedExpr_909_; lean_object* v_levelParams_910_; lean_object* v_nextLevelIdx_911_; lean_object* v_levelArgs_912_; lean_object* v_newLocalDecls_913_; lean_object* v_newLocalDeclsForMVars_914_; lean_object* v_newLetDecls_915_; lean_object* v_nextExprIdx_916_; lean_object* v_exprMVarArgs_917_; lean_object* v_exprFVarArgs_918_; lean_object* v_toProcess_919_; 
v_visitedExpr_909_ = lean_ctor_get(v___y_906_, 1);
lean_inc_ref(v_visitedExpr_909_);
v_levelParams_910_ = lean_ctor_get(v___y_906_, 2);
lean_inc_ref(v_levelParams_910_);
v_nextLevelIdx_911_ = lean_ctor_get(v___y_906_, 3);
lean_inc(v_nextLevelIdx_911_);
v_levelArgs_912_ = lean_ctor_get(v___y_906_, 4);
lean_inc_ref(v_levelArgs_912_);
v_newLocalDecls_913_ = lean_ctor_get(v___y_906_, 5);
lean_inc_ref(v_newLocalDecls_913_);
v_newLocalDeclsForMVars_914_ = lean_ctor_get(v___y_906_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_914_);
v_newLetDecls_915_ = lean_ctor_get(v___y_906_, 7);
lean_inc_ref(v_newLetDecls_915_);
v_nextExprIdx_916_ = lean_ctor_get(v___y_906_, 8);
lean_inc(v_nextExprIdx_916_);
v_exprMVarArgs_917_ = lean_ctor_get(v___y_906_, 9);
lean_inc_ref(v_exprMVarArgs_917_);
v_exprFVarArgs_918_ = lean_ctor_get(v___y_906_, 10);
lean_inc_ref(v_exprFVarArgs_918_);
v_toProcess_919_ = lean_ctor_get(v___y_906_, 11);
lean_inc_ref(v_toProcess_919_);
lean_dec_ref(v___y_906_);
v_visitedExpr_890_ = v_visitedExpr_909_;
v_levelParams_891_ = v_levelParams_910_;
v_nextLevelIdx_892_ = v_nextLevelIdx_911_;
v_levelArgs_893_ = v_levelArgs_912_;
v_newLocalDecls_894_ = v_newLocalDecls_913_;
v_newLocalDeclsForMVars_895_ = v_newLocalDeclsForMVars_914_;
v_newLetDecls_896_ = v_newLetDecls_915_;
v_nextExprIdx_897_ = v_nextExprIdx_916_;
v_exprMVarArgs_898_ = v_exprMVarArgs_917_;
v_exprFVarArgs_899_ = v_exprFVarArgs_918_;
v_toProcess_900_ = v_toProcess_919_;
v___y_901_ = v___y_907_;
v___y_902_ = v___y_908_;
goto v___jp_889_;
}
v___jp_920_:
{
lean_object* v_size_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_size_925_ = lean_ctor_get(v___y_921_, 0);
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_nat_add(v_size_925_, v___x_926_);
lean_inc(v___y_922_);
lean_inc(v_a_742_);
v___x_928_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_921_, v___x_927_, v_i_924_, v_a_742_, v___y_922_);
lean_dec(v_i_924_);
v___y_906_ = v___y_923_;
v___y_907_ = v___y_922_;
v___y_908_ = v___x_928_;
goto v___jp_905_;
}
v___jp_929_:
{
lean_object* v___x_933_; 
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v___y_932_, v_a_742_);
switch(lean_obj_tag(v___x_933_))
{
case 0:
{
lean_object* v_index_934_; lean_object* v_size_935_; lean_object* v___x_936_; 
v_index_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_index_934_);
lean_dec_ref_known(v___x_933_, 3);
v_size_935_ = lean_ctor_get(v___y_932_, 0);
lean_inc(v_size_935_);
lean_inc(v___y_930_);
lean_inc(v_a_742_);
v___x_936_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_932_, v_size_935_, v_index_934_, v_a_742_, v___y_930_);
lean_dec(v_index_934_);
v___y_906_ = v___y_931_;
v___y_907_ = v___y_930_;
v___y_908_ = v___x_936_;
goto v___jp_905_;
}
case 1:
{
lean_object* v_index_937_; 
v_index_937_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_index_937_);
lean_dec_ref_known(v___x_933_, 1);
v___y_921_ = v___y_932_;
v___y_922_ = v___y_930_;
v___y_923_ = v___y_931_;
v_i_924_ = v_index_937_;
goto v___jp_920_;
}
default: 
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_932_, v___x_938_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_index_940_; 
v_index_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_index_940_);
lean_dec_ref_known(v___x_939_, 1);
v___y_921_ = v___y_932_;
v___y_922_ = v___y_930_;
v___y_923_ = v___y_931_;
v_i_924_ = v_index_940_;
goto v___jp_920_;
}
else
{
v___y_906_ = v___y_931_;
v___y_907_ = v___y_930_;
v___y_908_ = v___y_932_;
goto v___jp_905_;
}
}
}
}
v___jp_941_:
{
lean_object* v_size_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_size_946_ = lean_ctor_get(v___y_942_, 0);
v___x_947_ = lean_unsigned_to_nat(1u);
v___x_948_ = lean_nat_add(v_size_946_, v___x_947_);
lean_inc(v___y_943_);
lean_inc(v_a_742_);
v___x_949_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_942_, v___x_948_, v_i_945_, v_a_742_, v___y_943_);
lean_dec(v_i_945_);
v___y_906_ = v___y_944_;
v___y_907_ = v___y_943_;
v___y_908_ = v___x_949_;
goto v___jp_905_;
}
v___jp_950_:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v___y_951_);
lean_dec_ref(v___y_951_);
v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v___x_954_, v_a_742_);
switch(lean_obj_tag(v___x_955_))
{
case 0:
{
lean_object* v_index_956_; lean_object* v_size_957_; lean_object* v___x_958_; 
v_index_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_index_956_);
lean_dec_ref_known(v___x_955_, 3);
v_size_957_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_size_957_);
lean_inc(v___y_952_);
lean_inc(v_a_742_);
v___x_958_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_954_, v_size_957_, v_index_956_, v_a_742_, v___y_952_);
lean_dec(v_index_956_);
v___y_906_ = v___y_953_;
v___y_907_ = v___y_952_;
v___y_908_ = v___x_958_;
goto v___jp_905_;
}
case 1:
{
lean_object* v_index_959_; 
v_index_959_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_index_959_);
lean_dec_ref_known(v___x_955_, 1);
v___y_942_ = v___x_954_;
v___y_943_ = v___y_952_;
v___y_944_ = v___y_953_;
v_i_945_ = v_index_959_;
goto v___jp_941_;
}
default: 
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_954_, v___x_960_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_index_962_; 
v_index_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_index_962_);
lean_dec_ref_known(v___x_961_, 1);
v___y_942_ = v___x_954_;
v___y_943_ = v___y_952_;
v___y_944_ = v___y_953_;
v_i_945_ = v_index_962_;
goto v___jp_941_;
}
else
{
v___y_906_ = v___y_953_;
v___y_907_ = v___y_952_;
v___y_908_ = v___x_954_;
goto v___jp_905_;
}
}
}
}
v___jp_963_:
{
lean_object* v___x_964_; lean_object* v_visitedLevel_965_; lean_object* v___x_966_; 
v___x_964_ = lean_st_ref_get(v_a_587_);
v_visitedLevel_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc_ref(v_visitedLevel_965_);
lean_dec(v___x_964_);
v___x_966_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_965_, v_a_742_);
lean_dec_ref(v_visitedLevel_965_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v___x_967_; 
lean_inc(v_a_742_);
v___x_967_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_742_, v_a_587_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; lean_object* v_visitedLevel_970_; lean_object* v_visitedExpr_971_; lean_object* v_levelParams_972_; lean_object* v_nextLevelIdx_973_; lean_object* v_levelArgs_974_; lean_object* v_newLocalDecls_975_; lean_object* v_newLocalDeclsForMVars_976_; lean_object* v_newLetDecls_977_; lean_object* v_nextExprIdx_978_; lean_object* v_exprMVarArgs_979_; lean_object* v_exprFVarArgs_980_; lean_object* v_toProcess_981_; lean_object* v___x_982_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = lean_st_ref_take(v_a_587_);
v_visitedLevel_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_visitedLevel_970_);
v_visitedExpr_971_ = lean_ctor_get(v___x_969_, 1);
lean_inc_ref(v_visitedExpr_971_);
v_levelParams_972_ = lean_ctor_get(v___x_969_, 2);
lean_inc_ref(v_levelParams_972_);
v_nextLevelIdx_973_ = lean_ctor_get(v___x_969_, 3);
lean_inc(v_nextLevelIdx_973_);
v_levelArgs_974_ = lean_ctor_get(v___x_969_, 4);
lean_inc_ref(v_levelArgs_974_);
v_newLocalDecls_975_ = lean_ctor_get(v___x_969_, 5);
lean_inc_ref(v_newLocalDecls_975_);
v_newLocalDeclsForMVars_976_ = lean_ctor_get(v___x_969_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_976_);
v_newLetDecls_977_ = lean_ctor_get(v___x_969_, 7);
lean_inc_ref(v_newLetDecls_977_);
v_nextExprIdx_978_ = lean_ctor_get(v___x_969_, 8);
lean_inc(v_nextExprIdx_978_);
v_exprMVarArgs_979_ = lean_ctor_get(v___x_969_, 9);
lean_inc_ref(v_exprMVarArgs_979_);
v_exprFVarArgs_980_ = lean_ctor_get(v___x_969_, 10);
lean_inc_ref(v_exprFVarArgs_980_);
v_toProcess_981_ = lean_ctor_get(v___x_969_, 11);
lean_inc_ref(v_toProcess_981_);
v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_970_, v_a_742_);
switch(lean_obj_tag(v___x_982_))
{
case 0:
{
lean_object* v_index_983_; lean_object* v_size_984_; lean_object* v___x_985_; 
lean_dec(v___x_969_);
v_index_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_index_983_);
lean_dec_ref_known(v___x_982_, 3);
v_size_984_ = lean_ctor_get(v_visitedLevel_970_, 0);
lean_inc(v_size_984_);
lean_inc(v_a_968_);
lean_inc(v_a_742_);
v___x_985_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_970_, v_size_984_, v_index_983_, v_a_742_, v_a_968_);
lean_dec(v_index_983_);
v_visitedExpr_890_ = v_visitedExpr_971_;
v_levelParams_891_ = v_levelParams_972_;
v_nextLevelIdx_892_ = v_nextLevelIdx_973_;
v_levelArgs_893_ = v_levelArgs_974_;
v_newLocalDecls_894_ = v_newLocalDecls_975_;
v_newLocalDeclsForMVars_895_ = v_newLocalDeclsForMVars_976_;
v_newLetDecls_896_ = v_newLetDecls_977_;
v_nextExprIdx_897_ = v_nextExprIdx_978_;
v_exprMVarArgs_898_ = v_exprMVarArgs_979_;
v_exprFVarArgs_899_ = v_exprFVarArgs_980_;
v_toProcess_900_ = v_toProcess_981_;
v___y_901_ = v_a_968_;
v___y_902_ = v___x_985_;
goto v___jp_889_;
}
case 1:
{
lean_object* v_index_986_; lean_object* v_size_987_; lean_object* v_keyArray_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v_index_986_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_index_986_);
lean_dec_ref_known(v___x_982_, 1);
v_size_987_ = lean_ctor_get(v_visitedLevel_970_, 0);
v_keyArray_988_ = lean_ctor_get(v_visitedLevel_970_, 1);
v___x_989_ = lean_unsigned_to_nat(1u);
v___x_990_ = lean_nat_add(v_size_987_, v___x_989_);
v___x_991_ = lean_array_get_size(v_keyArray_988_);
v___x_992_ = lean_nat_dec_lt(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_dec(v___x_990_);
lean_dec(v_index_986_);
lean_dec_ref(v_toProcess_981_);
lean_dec_ref(v_exprFVarArgs_980_);
lean_dec_ref(v_exprMVarArgs_979_);
lean_dec(v_nextExprIdx_978_);
lean_dec_ref(v_newLetDecls_977_);
lean_dec_ref(v_newLocalDeclsForMVars_976_);
lean_dec_ref(v_newLocalDecls_975_);
lean_dec_ref(v_levelArgs_974_);
lean_dec(v_nextLevelIdx_973_);
lean_dec_ref(v_levelParams_972_);
lean_dec_ref(v_visitedExpr_971_);
v___y_951_ = v_visitedLevel_970_;
v___y_952_ = v_a_968_;
v___y_953_ = v___x_969_;
goto v___jp_950_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_993_ = lean_unsigned_to_nat(4u);
v___x_994_ = lean_nat_mul(v___x_990_, v___x_993_);
v___x_995_ = lean_unsigned_to_nat(3u);
v___x_996_ = lean_nat_mul(v___x_991_, v___x_995_);
v___x_997_ = lean_nat_dec_le(v___x_994_, v___x_996_);
lean_dec(v___x_996_);
lean_dec(v___x_994_);
if (v___x_997_ == 0)
{
lean_dec(v___x_990_);
lean_dec(v_index_986_);
lean_dec_ref(v_toProcess_981_);
lean_dec_ref(v_exprFVarArgs_980_);
lean_dec_ref(v_exprMVarArgs_979_);
lean_dec(v_nextExprIdx_978_);
lean_dec_ref(v_newLetDecls_977_);
lean_dec_ref(v_newLocalDeclsForMVars_976_);
lean_dec_ref(v_newLocalDecls_975_);
lean_dec_ref(v_levelArgs_974_);
lean_dec(v_nextLevelIdx_973_);
lean_dec_ref(v_levelParams_972_);
lean_dec_ref(v_visitedExpr_971_);
v___y_951_ = v_visitedLevel_970_;
v___y_952_ = v_a_968_;
v___y_953_ = v___x_969_;
goto v___jp_950_;
}
else
{
lean_object* v___x_998_; 
lean_dec(v___x_969_);
lean_inc(v_a_968_);
lean_inc(v_a_742_);
v___x_998_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_970_, v___x_990_, v_index_986_, v_a_742_, v_a_968_);
lean_dec(v_index_986_);
v_visitedExpr_890_ = v_visitedExpr_971_;
v_levelParams_891_ = v_levelParams_972_;
v_nextLevelIdx_892_ = v_nextLevelIdx_973_;
v_levelArgs_893_ = v_levelArgs_974_;
v_newLocalDecls_894_ = v_newLocalDecls_975_;
v_newLocalDeclsForMVars_895_ = v_newLocalDeclsForMVars_976_;
v_newLetDecls_896_ = v_newLetDecls_977_;
v_nextExprIdx_897_ = v_nextExprIdx_978_;
v_exprMVarArgs_898_ = v_exprMVarArgs_979_;
v_exprFVarArgs_899_ = v_exprFVarArgs_980_;
v_toProcess_900_ = v_toProcess_981_;
v___y_901_ = v_a_968_;
v___y_902_ = v___x_998_;
goto v___jp_889_;
}
}
}
default: 
{
lean_object* v_size_999_; lean_object* v_keyArray_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
lean_dec_ref(v_toProcess_981_);
lean_dec_ref(v_exprFVarArgs_980_);
lean_dec_ref(v_exprMVarArgs_979_);
lean_dec(v_nextExprIdx_978_);
lean_dec_ref(v_newLetDecls_977_);
lean_dec_ref(v_newLocalDeclsForMVars_976_);
lean_dec_ref(v_newLocalDecls_975_);
lean_dec_ref(v_levelArgs_974_);
lean_dec(v_nextLevelIdx_973_);
lean_dec_ref(v_levelParams_972_);
lean_dec_ref(v_visitedExpr_971_);
v_size_999_ = lean_ctor_get(v_visitedLevel_970_, 0);
v_keyArray_1000_ = lean_ctor_get(v_visitedLevel_970_, 1);
v___x_1001_ = lean_unsigned_to_nat(1u);
v___x_1002_ = lean_nat_add(v_size_999_, v___x_1001_);
v___x_1003_ = lean_array_get_size(v_keyArray_1000_);
v___x_1004_ = lean_nat_dec_lt(v___x_1002_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
lean_dec(v___x_1002_);
v___x_1005_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_visitedLevel_970_);
lean_dec_ref(v_visitedLevel_970_);
v___y_930_ = v_a_968_;
v___y_931_ = v___x_969_;
v___y_932_ = v___x_1005_;
goto v___jp_929_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1006_ = lean_unsigned_to_nat(4u);
v___x_1007_ = lean_nat_mul(v___x_1002_, v___x_1006_);
lean_dec(v___x_1002_);
v___x_1008_ = lean_unsigned_to_nat(3u);
v___x_1009_ = lean_nat_mul(v___x_1003_, v___x_1008_);
v___x_1010_ = lean_nat_dec_le(v___x_1007_, v___x_1009_);
lean_dec(v___x_1009_);
lean_dec(v___x_1007_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_visitedLevel_970_);
lean_dec_ref(v_visitedLevel_970_);
v___y_930_ = v_a_968_;
v___y_931_ = v___x_969_;
v___y_932_ = v___x_1011_;
goto v___jp_929_;
}
else
{
v___y_930_ = v_a_968_;
v___y_931_ = v___x_969_;
v___y_932_ = v_visitedLevel_970_;
goto v___jp_929_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_1012_; 
v_a_1012_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_967_, 1);
v_a_886_ = v_a_1012_;
goto v___jp_885_;
}
else
{
lean_dec_ref_known(v_x_586_, 2);
return v___x_967_;
}
}
}
else
{
lean_object* v_val_1013_; 
v_val_1013_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v___x_966_, 1);
v_a_886_ = v_val_1013_;
goto v___jp_885_;
}
}
}
case 3:
{
lean_object* v_a_1016_; lean_object* v_a_1017_; lean_object* v___y_1019_; lean_object* v_a_1020_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v_visitedExpr_1030_; lean_object* v_levelParams_1031_; lean_object* v_nextLevelIdx_1032_; lean_object* v_levelArgs_1033_; lean_object* v_newLocalDecls_1034_; lean_object* v_newLocalDeclsForMVars_1035_; lean_object* v_newLetDecls_1036_; lean_object* v_nextExprIdx_1037_; lean_object* v_exprMVarArgs_1038_; lean_object* v_exprFVarArgs_1039_; lean_object* v_toProcess_1040_; lean_object* v___y_1041_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v_i_1065_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v_i_1088_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1108_; lean_object* v_a_1160_; lean_object* v_visitedExpr_1164_; lean_object* v_levelParams_1165_; lean_object* v_nextLevelIdx_1166_; lean_object* v_levelArgs_1167_; lean_object* v_newLocalDecls_1168_; lean_object* v_newLocalDeclsForMVars_1169_; lean_object* v_newLetDecls_1170_; lean_object* v_nextExprIdx_1171_; lean_object* v_exprMVarArgs_1172_; lean_object* v_exprFVarArgs_1173_; lean_object* v_toProcess_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v_i_1198_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v_i_1219_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; uint8_t v___x_1288_; 
v_a_1016_ = lean_ctor_get(v_x_586_, 0);
v_a_1017_ = lean_ctor_get(v_x_586_, 1);
v___x_1288_ = l_Lean_Level_hasMVar(v_a_1016_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = l_Lean_Level_hasParam(v_a_1016_);
if (v___x_1289_ == 0)
{
lean_inc(v_a_1016_);
v_a_1160_ = v_a_1016_;
goto v___jp_1159_;
}
else
{
goto v___jp_1237_;
}
}
else
{
goto v___jp_1237_;
}
v___jp_1018_:
{
size_t v___x_1021_; size_t v___x_1022_; uint8_t v___x_1023_; 
v___x_1021_ = lean_ptr_addr(v_a_1016_);
v___x_1022_ = lean_ptr_addr(v___y_1019_);
v___x_1023_ = lean_usize_dec_eq(v___x_1021_, v___x_1022_);
if (v___x_1023_ == 0)
{
v___y_598_ = v___y_1019_;
v___y_599_ = v_a_1020_;
v___y_600_ = v___x_1023_;
goto v___jp_597_;
}
else
{
size_t v___x_1024_; size_t v___x_1025_; uint8_t v___x_1026_; 
v___x_1024_ = lean_ptr_addr(v_a_1017_);
v___x_1025_ = lean_ptr_addr(v_a_1020_);
v___x_1026_ = lean_usize_dec_eq(v___x_1024_, v___x_1025_);
v___y_598_ = v___y_1019_;
v___y_599_ = v_a_1020_;
v___y_600_ = v___x_1026_;
goto v___jp_597_;
}
}
v___jp_1027_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1042_, 0, v___y_1041_);
lean_ctor_set(v___x_1042_, 1, v_visitedExpr_1030_);
lean_ctor_set(v___x_1042_, 2, v_levelParams_1031_);
lean_ctor_set(v___x_1042_, 3, v_nextLevelIdx_1032_);
lean_ctor_set(v___x_1042_, 4, v_levelArgs_1033_);
lean_ctor_set(v___x_1042_, 5, v_newLocalDecls_1034_);
lean_ctor_set(v___x_1042_, 6, v_newLocalDeclsForMVars_1035_);
lean_ctor_set(v___x_1042_, 7, v_newLetDecls_1036_);
lean_ctor_set(v___x_1042_, 8, v_nextExprIdx_1037_);
lean_ctor_set(v___x_1042_, 9, v_exprMVarArgs_1038_);
lean_ctor_set(v___x_1042_, 10, v_exprFVarArgs_1039_);
lean_ctor_set(v___x_1042_, 11, v_toProcess_1040_);
v___x_1043_ = lean_st_ref_put(v_a_587_, v___x_1042_);
v___y_1019_ = v___y_1028_;
v_a_1020_ = v___y_1029_;
goto v___jp_1018_;
}
v___jp_1044_:
{
lean_object* v_visitedExpr_1049_; lean_object* v_levelParams_1050_; lean_object* v_nextLevelIdx_1051_; lean_object* v_levelArgs_1052_; lean_object* v_newLocalDecls_1053_; lean_object* v_newLocalDeclsForMVars_1054_; lean_object* v_newLetDecls_1055_; lean_object* v_nextExprIdx_1056_; lean_object* v_exprMVarArgs_1057_; lean_object* v_exprFVarArgs_1058_; lean_object* v_toProcess_1059_; 
v_visitedExpr_1049_ = lean_ctor_get(v___y_1047_, 1);
lean_inc_ref(v_visitedExpr_1049_);
v_levelParams_1050_ = lean_ctor_get(v___y_1047_, 2);
lean_inc_ref(v_levelParams_1050_);
v_nextLevelIdx_1051_ = lean_ctor_get(v___y_1047_, 3);
lean_inc(v_nextLevelIdx_1051_);
v_levelArgs_1052_ = lean_ctor_get(v___y_1047_, 4);
lean_inc_ref(v_levelArgs_1052_);
v_newLocalDecls_1053_ = lean_ctor_get(v___y_1047_, 5);
lean_inc_ref(v_newLocalDecls_1053_);
v_newLocalDeclsForMVars_1054_ = lean_ctor_get(v___y_1047_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_1054_);
v_newLetDecls_1055_ = lean_ctor_get(v___y_1047_, 7);
lean_inc_ref(v_newLetDecls_1055_);
v_nextExprIdx_1056_ = lean_ctor_get(v___y_1047_, 8);
lean_inc(v_nextExprIdx_1056_);
v_exprMVarArgs_1057_ = lean_ctor_get(v___y_1047_, 9);
lean_inc_ref(v_exprMVarArgs_1057_);
v_exprFVarArgs_1058_ = lean_ctor_get(v___y_1047_, 10);
lean_inc_ref(v_exprFVarArgs_1058_);
v_toProcess_1059_ = lean_ctor_get(v___y_1047_, 11);
lean_inc_ref(v_toProcess_1059_);
lean_dec_ref(v___y_1047_);
v___y_1028_ = v___y_1045_;
v___y_1029_ = v___y_1046_;
v_visitedExpr_1030_ = v_visitedExpr_1049_;
v_levelParams_1031_ = v_levelParams_1050_;
v_nextLevelIdx_1032_ = v_nextLevelIdx_1051_;
v_levelArgs_1033_ = v_levelArgs_1052_;
v_newLocalDecls_1034_ = v_newLocalDecls_1053_;
v_newLocalDeclsForMVars_1035_ = v_newLocalDeclsForMVars_1054_;
v_newLetDecls_1036_ = v_newLetDecls_1055_;
v_nextExprIdx_1037_ = v_nextExprIdx_1056_;
v_exprMVarArgs_1038_ = v_exprMVarArgs_1057_;
v_exprFVarArgs_1039_ = v_exprFVarArgs_1058_;
v_toProcess_1040_ = v_toProcess_1059_;
v___y_1041_ = v___y_1048_;
goto v___jp_1027_;
}
v___jp_1060_:
{
lean_object* v_size_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_size_1066_ = lean_ctor_get(v___y_1061_, 0);
v___x_1067_ = lean_unsigned_to_nat(1u);
v___x_1068_ = lean_nat_add(v_size_1066_, v___x_1067_);
lean_inc(v___y_1063_);
lean_inc(v_a_1017_);
v___x_1069_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1061_, v___x_1068_, v_i_1065_, v_a_1017_, v___y_1063_);
lean_dec(v_i_1065_);
v___y_1045_ = v___y_1062_;
v___y_1046_ = v___y_1063_;
v___y_1047_ = v___y_1064_;
v___y_1048_ = v___x_1069_;
goto v___jp_1044_;
}
v___jp_1070_:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v___y_1074_, v_a_1017_);
switch(lean_obj_tag(v___x_1075_))
{
case 0:
{
lean_object* v_index_1076_; lean_object* v_size_1077_; lean_object* v___x_1078_; 
v_index_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_index_1076_);
lean_dec_ref_known(v___x_1075_, 3);
v_size_1077_ = lean_ctor_get(v___y_1074_, 0);
lean_inc(v_size_1077_);
lean_inc(v___y_1072_);
lean_inc(v_a_1017_);
v___x_1078_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1074_, v_size_1077_, v_index_1076_, v_a_1017_, v___y_1072_);
lean_dec(v_index_1076_);
v___y_1045_ = v___y_1071_;
v___y_1046_ = v___y_1072_;
v___y_1047_ = v___y_1073_;
v___y_1048_ = v___x_1078_;
goto v___jp_1044_;
}
case 1:
{
lean_object* v_index_1079_; 
v_index_1079_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_index_1079_);
lean_dec_ref_known(v___x_1075_, 1);
v___y_1061_ = v___y_1074_;
v___y_1062_ = v___y_1071_;
v___y_1063_ = v___y_1072_;
v___y_1064_ = v___y_1073_;
v_i_1065_ = v_index_1079_;
goto v___jp_1060_;
}
default: 
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1074_, v___x_1080_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_index_1082_; 
v_index_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_index_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___y_1061_ = v___y_1074_;
v___y_1062_ = v___y_1071_;
v___y_1063_ = v___y_1072_;
v___y_1064_ = v___y_1073_;
v_i_1065_ = v_index_1082_;
goto v___jp_1060_;
}
else
{
v___y_1045_ = v___y_1071_;
v___y_1046_ = v___y_1072_;
v___y_1047_ = v___y_1073_;
v___y_1048_ = v___y_1074_;
goto v___jp_1044_;
}
}
}
}
v___jp_1083_:
{
lean_object* v_size_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_size_1089_ = lean_ctor_get(v___y_1085_, 0);
v___x_1090_ = lean_unsigned_to_nat(1u);
v___x_1091_ = lean_nat_add(v_size_1089_, v___x_1090_);
lean_inc(v___y_1086_);
lean_inc(v_a_1017_);
v___x_1092_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1085_, v___x_1091_, v_i_1088_, v_a_1017_, v___y_1086_);
lean_dec(v_i_1088_);
v___y_1045_ = v___y_1084_;
v___y_1046_ = v___y_1086_;
v___y_1047_ = v___y_1087_;
v___y_1048_ = v___x_1092_;
goto v___jp_1044_;
}
v___jp_1093_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v___y_1094_);
lean_dec_ref(v___y_1094_);
v___x_1099_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v___x_1098_, v_a_1017_);
switch(lean_obj_tag(v___x_1099_))
{
case 0:
{
lean_object* v_index_1100_; lean_object* v_size_1101_; lean_object* v___x_1102_; 
v_index_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_index_1100_);
lean_dec_ref_known(v___x_1099_, 3);
v_size_1101_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_size_1101_);
lean_inc(v___y_1096_);
lean_inc(v_a_1017_);
v___x_1102_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1098_, v_size_1101_, v_index_1100_, v_a_1017_, v___y_1096_);
lean_dec(v_index_1100_);
v___y_1045_ = v___y_1095_;
v___y_1046_ = v___y_1096_;
v___y_1047_ = v___y_1097_;
v___y_1048_ = v___x_1102_;
goto v___jp_1044_;
}
case 1:
{
lean_object* v_index_1103_; 
v_index_1103_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_index_1103_);
lean_dec_ref_known(v___x_1099_, 1);
v___y_1084_ = v___y_1095_;
v___y_1085_ = v___x_1098_;
v___y_1086_ = v___y_1096_;
v___y_1087_ = v___y_1097_;
v_i_1088_ = v_index_1103_;
goto v___jp_1083_;
}
default: 
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1098_, v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_index_1106_; 
v_index_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_index_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v___y_1084_ = v___y_1095_;
v___y_1085_ = v___x_1098_;
v___y_1086_ = v___y_1096_;
v___y_1087_ = v___y_1097_;
v_i_1088_ = v_index_1106_;
goto v___jp_1083_;
}
else
{
v___y_1045_ = v___y_1095_;
v___y_1046_ = v___y_1096_;
v___y_1047_ = v___y_1097_;
v___y_1048_ = v___x_1098_;
goto v___jp_1044_;
}
}
}
}
v___jp_1107_:
{
lean_object* v___x_1109_; lean_object* v_visitedLevel_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_st_ref_get(v_a_587_);
v_visitedLevel_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_ref(v_visitedLevel_1110_);
lean_dec(v___x_1109_);
v___x_1111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_1110_, v_a_1017_);
lean_dec_ref(v_visitedLevel_1110_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1112_; 
lean_inc(v_a_1017_);
v___x_1112_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_1017_, v_a_587_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; lean_object* v_visitedLevel_1115_; lean_object* v_visitedExpr_1116_; lean_object* v_levelParams_1117_; lean_object* v_nextLevelIdx_1118_; lean_object* v_levelArgs_1119_; lean_object* v_newLocalDecls_1120_; lean_object* v_newLocalDeclsForMVars_1121_; lean_object* v_newLetDecls_1122_; lean_object* v_nextExprIdx_1123_; lean_object* v_exprMVarArgs_1124_; lean_object* v_exprFVarArgs_1125_; lean_object* v_toProcess_1126_; lean_object* v___x_1127_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v___x_1114_ = lean_st_ref_take(v_a_587_);
v_visitedLevel_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_visitedLevel_1115_);
v_visitedExpr_1116_ = lean_ctor_get(v___x_1114_, 1);
lean_inc_ref(v_visitedExpr_1116_);
v_levelParams_1117_ = lean_ctor_get(v___x_1114_, 2);
lean_inc_ref(v_levelParams_1117_);
v_nextLevelIdx_1118_ = lean_ctor_get(v___x_1114_, 3);
lean_inc(v_nextLevelIdx_1118_);
v_levelArgs_1119_ = lean_ctor_get(v___x_1114_, 4);
lean_inc_ref(v_levelArgs_1119_);
v_newLocalDecls_1120_ = lean_ctor_get(v___x_1114_, 5);
lean_inc_ref(v_newLocalDecls_1120_);
v_newLocalDeclsForMVars_1121_ = lean_ctor_get(v___x_1114_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_1121_);
v_newLetDecls_1122_ = lean_ctor_get(v___x_1114_, 7);
lean_inc_ref(v_newLetDecls_1122_);
v_nextExprIdx_1123_ = lean_ctor_get(v___x_1114_, 8);
lean_inc(v_nextExprIdx_1123_);
v_exprMVarArgs_1124_ = lean_ctor_get(v___x_1114_, 9);
lean_inc_ref(v_exprMVarArgs_1124_);
v_exprFVarArgs_1125_ = lean_ctor_get(v___x_1114_, 10);
lean_inc_ref(v_exprFVarArgs_1125_);
v_toProcess_1126_ = lean_ctor_get(v___x_1114_, 11);
lean_inc_ref(v_toProcess_1126_);
v___x_1127_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_1115_, v_a_1017_);
switch(lean_obj_tag(v___x_1127_))
{
case 0:
{
lean_object* v_index_1128_; lean_object* v_size_1129_; lean_object* v___x_1130_; 
lean_dec(v___x_1114_);
v_index_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_index_1128_);
lean_dec_ref_known(v___x_1127_, 3);
v_size_1129_ = lean_ctor_get(v_visitedLevel_1115_, 0);
lean_inc(v_size_1129_);
lean_inc(v_a_1113_);
lean_inc(v_a_1017_);
v___x_1130_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_1115_, v_size_1129_, v_index_1128_, v_a_1017_, v_a_1113_);
lean_dec(v_index_1128_);
v___y_1028_ = v___y_1108_;
v___y_1029_ = v_a_1113_;
v_visitedExpr_1030_ = v_visitedExpr_1116_;
v_levelParams_1031_ = v_levelParams_1117_;
v_nextLevelIdx_1032_ = v_nextLevelIdx_1118_;
v_levelArgs_1033_ = v_levelArgs_1119_;
v_newLocalDecls_1034_ = v_newLocalDecls_1120_;
v_newLocalDeclsForMVars_1035_ = v_newLocalDeclsForMVars_1121_;
v_newLetDecls_1036_ = v_newLetDecls_1122_;
v_nextExprIdx_1037_ = v_nextExprIdx_1123_;
v_exprMVarArgs_1038_ = v_exprMVarArgs_1124_;
v_exprFVarArgs_1039_ = v_exprFVarArgs_1125_;
v_toProcess_1040_ = v_toProcess_1126_;
v___y_1041_ = v___x_1130_;
goto v___jp_1027_;
}
case 1:
{
lean_object* v_index_1131_; lean_object* v_size_1132_; lean_object* v_keyArray_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v_index_1131_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_index_1131_);
lean_dec_ref_known(v___x_1127_, 1);
v_size_1132_ = lean_ctor_get(v_visitedLevel_1115_, 0);
v_keyArray_1133_ = lean_ctor_get(v_visitedLevel_1115_, 1);
v___x_1134_ = lean_unsigned_to_nat(1u);
v___x_1135_ = lean_nat_add(v_size_1132_, v___x_1134_);
v___x_1136_ = lean_array_get_size(v_keyArray_1133_);
v___x_1137_ = lean_nat_dec_lt(v___x_1135_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_dec(v___x_1135_);
lean_dec(v_index_1131_);
lean_dec_ref(v_toProcess_1126_);
lean_dec_ref(v_exprFVarArgs_1125_);
lean_dec_ref(v_exprMVarArgs_1124_);
lean_dec(v_nextExprIdx_1123_);
lean_dec_ref(v_newLetDecls_1122_);
lean_dec_ref(v_newLocalDeclsForMVars_1121_);
lean_dec_ref(v_newLocalDecls_1120_);
lean_dec_ref(v_levelArgs_1119_);
lean_dec(v_nextLevelIdx_1118_);
lean_dec_ref(v_levelParams_1117_);
lean_dec_ref(v_visitedExpr_1116_);
v___y_1094_ = v_visitedLevel_1115_;
v___y_1095_ = v___y_1108_;
v___y_1096_ = v_a_1113_;
v___y_1097_ = v___x_1114_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1138_ = lean_unsigned_to_nat(4u);
v___x_1139_ = lean_nat_mul(v___x_1135_, v___x_1138_);
v___x_1140_ = lean_unsigned_to_nat(3u);
v___x_1141_ = lean_nat_mul(v___x_1136_, v___x_1140_);
v___x_1142_ = lean_nat_dec_le(v___x_1139_, v___x_1141_);
lean_dec(v___x_1141_);
lean_dec(v___x_1139_);
if (v___x_1142_ == 0)
{
lean_dec(v___x_1135_);
lean_dec(v_index_1131_);
lean_dec_ref(v_toProcess_1126_);
lean_dec_ref(v_exprFVarArgs_1125_);
lean_dec_ref(v_exprMVarArgs_1124_);
lean_dec(v_nextExprIdx_1123_);
lean_dec_ref(v_newLetDecls_1122_);
lean_dec_ref(v_newLocalDeclsForMVars_1121_);
lean_dec_ref(v_newLocalDecls_1120_);
lean_dec_ref(v_levelArgs_1119_);
lean_dec(v_nextLevelIdx_1118_);
lean_dec_ref(v_levelParams_1117_);
lean_dec_ref(v_visitedExpr_1116_);
v___y_1094_ = v_visitedLevel_1115_;
v___y_1095_ = v___y_1108_;
v___y_1096_ = v_a_1113_;
v___y_1097_ = v___x_1114_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1143_; 
lean_dec(v___x_1114_);
lean_inc(v_a_1113_);
lean_inc(v_a_1017_);
v___x_1143_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_1115_, v___x_1135_, v_index_1131_, v_a_1017_, v_a_1113_);
lean_dec(v_index_1131_);
v___y_1028_ = v___y_1108_;
v___y_1029_ = v_a_1113_;
v_visitedExpr_1030_ = v_visitedExpr_1116_;
v_levelParams_1031_ = v_levelParams_1117_;
v_nextLevelIdx_1032_ = v_nextLevelIdx_1118_;
v_levelArgs_1033_ = v_levelArgs_1119_;
v_newLocalDecls_1034_ = v_newLocalDecls_1120_;
v_newLocalDeclsForMVars_1035_ = v_newLocalDeclsForMVars_1121_;
v_newLetDecls_1036_ = v_newLetDecls_1122_;
v_nextExprIdx_1037_ = v_nextExprIdx_1123_;
v_exprMVarArgs_1038_ = v_exprMVarArgs_1124_;
v_exprFVarArgs_1039_ = v_exprFVarArgs_1125_;
v_toProcess_1040_ = v_toProcess_1126_;
v___y_1041_ = v___x_1143_;
goto v___jp_1027_;
}
}
}
default: 
{
lean_object* v_size_1144_; lean_object* v_keyArray_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
lean_dec_ref(v_toProcess_1126_);
lean_dec_ref(v_exprFVarArgs_1125_);
lean_dec_ref(v_exprMVarArgs_1124_);
lean_dec(v_nextExprIdx_1123_);
lean_dec_ref(v_newLetDecls_1122_);
lean_dec_ref(v_newLocalDeclsForMVars_1121_);
lean_dec_ref(v_newLocalDecls_1120_);
lean_dec_ref(v_levelArgs_1119_);
lean_dec(v_nextLevelIdx_1118_);
lean_dec_ref(v_levelParams_1117_);
lean_dec_ref(v_visitedExpr_1116_);
v_size_1144_ = lean_ctor_get(v_visitedLevel_1115_, 0);
v_keyArray_1145_ = lean_ctor_get(v_visitedLevel_1115_, 1);
v___x_1146_ = lean_unsigned_to_nat(1u);
v___x_1147_ = lean_nat_add(v_size_1144_, v___x_1146_);
v___x_1148_ = lean_array_get_size(v_keyArray_1145_);
v___x_1149_ = lean_nat_dec_lt(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_dec(v___x_1147_);
v___x_1150_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_visitedLevel_1115_);
lean_dec_ref(v_visitedLevel_1115_);
v___y_1071_ = v___y_1108_;
v___y_1072_ = v_a_1113_;
v___y_1073_ = v___x_1114_;
v___y_1074_ = v___x_1150_;
goto v___jp_1070_;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1151_ = lean_unsigned_to_nat(4u);
v___x_1152_ = lean_nat_mul(v___x_1147_, v___x_1151_);
lean_dec(v___x_1147_);
v___x_1153_ = lean_unsigned_to_nat(3u);
v___x_1154_ = lean_nat_mul(v___x_1148_, v___x_1153_);
v___x_1155_ = lean_nat_dec_le(v___x_1152_, v___x_1154_);
lean_dec(v___x_1154_);
lean_dec(v___x_1152_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_visitedLevel_1115_);
lean_dec_ref(v_visitedLevel_1115_);
v___y_1071_ = v___y_1108_;
v___y_1072_ = v_a_1113_;
v___y_1073_ = v___x_1114_;
v___y_1074_ = v___x_1156_;
goto v___jp_1070_;
}
else
{
v___y_1071_ = v___y_1108_;
v___y_1072_ = v_a_1113_;
v___y_1073_ = v___x_1114_;
v___y_1074_ = v_visitedLevel_1115_;
goto v___jp_1070_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1157_; 
v_a_1157_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1112_, 1);
v___y_1019_ = v___y_1108_;
v_a_1020_ = v_a_1157_;
goto v___jp_1018_;
}
else
{
lean_dec(v___y_1108_);
lean_dec_ref_known(v_x_586_, 2);
return v___x_1112_;
}
}
}
else
{
lean_object* v_val_1158_; 
v_val_1158_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_val_1158_);
lean_dec_ref_known(v___x_1111_, 1);
v___y_1019_ = v___y_1108_;
v_a_1020_ = v_val_1158_;
goto v___jp_1018_;
}
}
v___jp_1159_:
{
uint8_t v___x_1161_; 
v___x_1161_ = l_Lean_Level_hasMVar(v_a_1017_);
if (v___x_1161_ == 0)
{
uint8_t v___x_1162_; 
v___x_1162_ = l_Lean_Level_hasParam(v_a_1017_);
if (v___x_1162_ == 0)
{
lean_inc(v_a_1017_);
v___y_1019_ = v_a_1160_;
v_a_1020_ = v_a_1017_;
goto v___jp_1018_;
}
else
{
v___y_1108_ = v_a_1160_;
goto v___jp_1107_;
}
}
else
{
v___y_1108_ = v_a_1160_;
goto v___jp_1107_;
}
}
v___jp_1163_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1177_, 0, v___y_1176_);
lean_ctor_set(v___x_1177_, 1, v_visitedExpr_1164_);
lean_ctor_set(v___x_1177_, 2, v_levelParams_1165_);
lean_ctor_set(v___x_1177_, 3, v_nextLevelIdx_1166_);
lean_ctor_set(v___x_1177_, 4, v_levelArgs_1167_);
lean_ctor_set(v___x_1177_, 5, v_newLocalDecls_1168_);
lean_ctor_set(v___x_1177_, 6, v_newLocalDeclsForMVars_1169_);
lean_ctor_set(v___x_1177_, 7, v_newLetDecls_1170_);
lean_ctor_set(v___x_1177_, 8, v_nextExprIdx_1171_);
lean_ctor_set(v___x_1177_, 9, v_exprMVarArgs_1172_);
lean_ctor_set(v___x_1177_, 10, v_exprFVarArgs_1173_);
lean_ctor_set(v___x_1177_, 11, v_toProcess_1174_);
v___x_1178_ = lean_st_ref_put(v_a_587_, v___x_1177_);
v_a_1160_ = v___y_1175_;
goto v___jp_1159_;
}
v___jp_1179_:
{
lean_object* v_visitedExpr_1183_; lean_object* v_levelParams_1184_; lean_object* v_nextLevelIdx_1185_; lean_object* v_levelArgs_1186_; lean_object* v_newLocalDecls_1187_; lean_object* v_newLocalDeclsForMVars_1188_; lean_object* v_newLetDecls_1189_; lean_object* v_nextExprIdx_1190_; lean_object* v_exprMVarArgs_1191_; lean_object* v_exprFVarArgs_1192_; lean_object* v_toProcess_1193_; 
v_visitedExpr_1183_ = lean_ctor_get(v___y_1180_, 1);
lean_inc_ref(v_visitedExpr_1183_);
v_levelParams_1184_ = lean_ctor_get(v___y_1180_, 2);
lean_inc_ref(v_levelParams_1184_);
v_nextLevelIdx_1185_ = lean_ctor_get(v___y_1180_, 3);
lean_inc(v_nextLevelIdx_1185_);
v_levelArgs_1186_ = lean_ctor_get(v___y_1180_, 4);
lean_inc_ref(v_levelArgs_1186_);
v_newLocalDecls_1187_ = lean_ctor_get(v___y_1180_, 5);
lean_inc_ref(v_newLocalDecls_1187_);
v_newLocalDeclsForMVars_1188_ = lean_ctor_get(v___y_1180_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_1188_);
v_newLetDecls_1189_ = lean_ctor_get(v___y_1180_, 7);
lean_inc_ref(v_newLetDecls_1189_);
v_nextExprIdx_1190_ = lean_ctor_get(v___y_1180_, 8);
lean_inc(v_nextExprIdx_1190_);
v_exprMVarArgs_1191_ = lean_ctor_get(v___y_1180_, 9);
lean_inc_ref(v_exprMVarArgs_1191_);
v_exprFVarArgs_1192_ = lean_ctor_get(v___y_1180_, 10);
lean_inc_ref(v_exprFVarArgs_1192_);
v_toProcess_1193_ = lean_ctor_get(v___y_1180_, 11);
lean_inc_ref(v_toProcess_1193_);
lean_dec_ref(v___y_1180_);
v_visitedExpr_1164_ = v_visitedExpr_1183_;
v_levelParams_1165_ = v_levelParams_1184_;
v_nextLevelIdx_1166_ = v_nextLevelIdx_1185_;
v_levelArgs_1167_ = v_levelArgs_1186_;
v_newLocalDecls_1168_ = v_newLocalDecls_1187_;
v_newLocalDeclsForMVars_1169_ = v_newLocalDeclsForMVars_1188_;
v_newLetDecls_1170_ = v_newLetDecls_1189_;
v_nextExprIdx_1171_ = v_nextExprIdx_1190_;
v_exprMVarArgs_1172_ = v_exprMVarArgs_1191_;
v_exprFVarArgs_1173_ = v_exprFVarArgs_1192_;
v_toProcess_1174_ = v_toProcess_1193_;
v___y_1175_ = v___y_1181_;
v___y_1176_ = v___y_1182_;
goto v___jp_1163_;
}
v___jp_1194_:
{
lean_object* v_size_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_size_1199_ = lean_ctor_get(v___y_1197_, 0);
v___x_1200_ = lean_unsigned_to_nat(1u);
v___x_1201_ = lean_nat_add(v_size_1199_, v___x_1200_);
lean_inc(v___y_1196_);
lean_inc(v_a_1016_);
v___x_1202_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1197_, v___x_1201_, v_i_1198_, v_a_1016_, v___y_1196_);
lean_dec(v_i_1198_);
v___y_1180_ = v___y_1195_;
v___y_1181_ = v___y_1196_;
v___y_1182_ = v___x_1202_;
goto v___jp_1179_;
}
v___jp_1203_:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v___y_1206_, v_a_1016_);
switch(lean_obj_tag(v___x_1207_))
{
case 0:
{
lean_object* v_index_1208_; lean_object* v_size_1209_; lean_object* v___x_1210_; 
v_index_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_index_1208_);
lean_dec_ref_known(v___x_1207_, 3);
v_size_1209_ = lean_ctor_get(v___y_1206_, 0);
lean_inc(v_size_1209_);
lean_inc(v___y_1205_);
lean_inc(v_a_1016_);
v___x_1210_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1206_, v_size_1209_, v_index_1208_, v_a_1016_, v___y_1205_);
lean_dec(v_index_1208_);
v___y_1180_ = v___y_1204_;
v___y_1181_ = v___y_1205_;
v___y_1182_ = v___x_1210_;
goto v___jp_1179_;
}
case 1:
{
lean_object* v_index_1211_; 
v_index_1211_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_index_1211_);
lean_dec_ref_known(v___x_1207_, 1);
v___y_1195_ = v___y_1204_;
v___y_1196_ = v___y_1205_;
v___y_1197_ = v___y_1206_;
v_i_1198_ = v_index_1211_;
goto v___jp_1194_;
}
default: 
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1206_, v___x_1212_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_index_1214_; 
v_index_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_index_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v___y_1195_ = v___y_1204_;
v___y_1196_ = v___y_1205_;
v___y_1197_ = v___y_1206_;
v_i_1198_ = v_index_1214_;
goto v___jp_1194_;
}
else
{
v___y_1180_ = v___y_1204_;
v___y_1181_ = v___y_1205_;
v___y_1182_ = v___y_1206_;
goto v___jp_1179_;
}
}
}
}
v___jp_1215_:
{
lean_object* v_size_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_size_1220_ = lean_ctor_get(v___y_1217_, 0);
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = lean_nat_add(v_size_1220_, v___x_1221_);
lean_inc(v___y_1218_);
lean_inc(v_a_1016_);
v___x_1223_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1217_, v___x_1222_, v_i_1219_, v_a_1016_, v___y_1218_);
lean_dec(v_i_1219_);
v___y_1180_ = v___y_1216_;
v___y_1181_ = v___y_1218_;
v___y_1182_ = v___x_1223_;
goto v___jp_1179_;
}
v___jp_1224_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v___y_1227_);
lean_dec_ref(v___y_1227_);
v___x_1229_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v___x_1228_, v_a_1016_);
switch(lean_obj_tag(v___x_1229_))
{
case 0:
{
lean_object* v_index_1230_; lean_object* v_size_1231_; lean_object* v___x_1232_; 
v_index_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_index_1230_);
lean_dec_ref_known(v___x_1229_, 3);
v_size_1231_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_size_1231_);
lean_inc(v___y_1226_);
lean_inc(v_a_1016_);
v___x_1232_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1228_, v_size_1231_, v_index_1230_, v_a_1016_, v___y_1226_);
lean_dec(v_index_1230_);
v___y_1180_ = v___y_1225_;
v___y_1181_ = v___y_1226_;
v___y_1182_ = v___x_1232_;
goto v___jp_1179_;
}
case 1:
{
lean_object* v_index_1233_; 
v_index_1233_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_index_1233_);
lean_dec_ref_known(v___x_1229_, 1);
v___y_1216_ = v___y_1225_;
v___y_1217_ = v___x_1228_;
v___y_1218_ = v___y_1226_;
v_i_1219_ = v_index_1233_;
goto v___jp_1215_;
}
default: 
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1228_, v___x_1234_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_index_1236_; 
v_index_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_index_1236_);
lean_dec_ref_known(v___x_1235_, 1);
v___y_1216_ = v___y_1225_;
v___y_1217_ = v___x_1228_;
v___y_1218_ = v___y_1226_;
v_i_1219_ = v_index_1236_;
goto v___jp_1215_;
}
else
{
v___y_1180_ = v___y_1225_;
v___y_1181_ = v___y_1226_;
v___y_1182_ = v___x_1228_;
goto v___jp_1179_;
}
}
}
}
v___jp_1237_:
{
lean_object* v___x_1238_; lean_object* v_visitedLevel_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_st_ref_get(v_a_587_);
v_visitedLevel_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc_ref(v_visitedLevel_1239_);
lean_dec(v___x_1238_);
v___x_1240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_1239_, v_a_1016_);
lean_dec_ref(v_visitedLevel_1239_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v___x_1241_; 
lean_inc(v_a_1016_);
v___x_1241_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_1016_, v_a_587_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v_visitedLevel_1244_; lean_object* v_visitedExpr_1245_; lean_object* v_levelParams_1246_; lean_object* v_nextLevelIdx_1247_; lean_object* v_levelArgs_1248_; lean_object* v_newLocalDecls_1249_; lean_object* v_newLocalDeclsForMVars_1250_; lean_object* v_newLetDecls_1251_; lean_object* v_nextExprIdx_1252_; lean_object* v_exprMVarArgs_1253_; lean_object* v_exprFVarArgs_1254_; lean_object* v_toProcess_1255_; lean_object* v___x_1256_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = lean_st_ref_take(v_a_587_);
v_visitedLevel_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc_ref(v_visitedLevel_1244_);
v_visitedExpr_1245_ = lean_ctor_get(v___x_1243_, 1);
lean_inc_ref(v_visitedExpr_1245_);
v_levelParams_1246_ = lean_ctor_get(v___x_1243_, 2);
lean_inc_ref(v_levelParams_1246_);
v_nextLevelIdx_1247_ = lean_ctor_get(v___x_1243_, 3);
lean_inc(v_nextLevelIdx_1247_);
v_levelArgs_1248_ = lean_ctor_get(v___x_1243_, 4);
lean_inc_ref(v_levelArgs_1248_);
v_newLocalDecls_1249_ = lean_ctor_get(v___x_1243_, 5);
lean_inc_ref(v_newLocalDecls_1249_);
v_newLocalDeclsForMVars_1250_ = lean_ctor_get(v___x_1243_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_1250_);
v_newLetDecls_1251_ = lean_ctor_get(v___x_1243_, 7);
lean_inc_ref(v_newLetDecls_1251_);
v_nextExprIdx_1252_ = lean_ctor_get(v___x_1243_, 8);
lean_inc(v_nextExprIdx_1252_);
v_exprMVarArgs_1253_ = lean_ctor_get(v___x_1243_, 9);
lean_inc_ref(v_exprMVarArgs_1253_);
v_exprFVarArgs_1254_ = lean_ctor_get(v___x_1243_, 10);
lean_inc_ref(v_exprFVarArgs_1254_);
v_toProcess_1255_ = lean_ctor_get(v___x_1243_, 11);
lean_inc_ref(v_toProcess_1255_);
v___x_1256_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_1244_, v_a_1016_);
switch(lean_obj_tag(v___x_1256_))
{
case 0:
{
lean_object* v_index_1257_; lean_object* v_size_1258_; lean_object* v___x_1259_; 
lean_dec(v___x_1243_);
v_index_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_index_1257_);
lean_dec_ref_known(v___x_1256_, 3);
v_size_1258_ = lean_ctor_get(v_visitedLevel_1244_, 0);
lean_inc(v_size_1258_);
lean_inc(v_a_1242_);
lean_inc(v_a_1016_);
v___x_1259_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_1244_, v_size_1258_, v_index_1257_, v_a_1016_, v_a_1242_);
lean_dec(v_index_1257_);
v_visitedExpr_1164_ = v_visitedExpr_1245_;
v_levelParams_1165_ = v_levelParams_1246_;
v_nextLevelIdx_1166_ = v_nextLevelIdx_1247_;
v_levelArgs_1167_ = v_levelArgs_1248_;
v_newLocalDecls_1168_ = v_newLocalDecls_1249_;
v_newLocalDeclsForMVars_1169_ = v_newLocalDeclsForMVars_1250_;
v_newLetDecls_1170_ = v_newLetDecls_1251_;
v_nextExprIdx_1171_ = v_nextExprIdx_1252_;
v_exprMVarArgs_1172_ = v_exprMVarArgs_1253_;
v_exprFVarArgs_1173_ = v_exprFVarArgs_1254_;
v_toProcess_1174_ = v_toProcess_1255_;
v___y_1175_ = v_a_1242_;
v___y_1176_ = v___x_1259_;
goto v___jp_1163_;
}
case 1:
{
lean_object* v_index_1260_; lean_object* v_size_1261_; lean_object* v_keyArray_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v_index_1260_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_index_1260_);
lean_dec_ref_known(v___x_1256_, 1);
v_size_1261_ = lean_ctor_get(v_visitedLevel_1244_, 0);
v_keyArray_1262_ = lean_ctor_get(v_visitedLevel_1244_, 1);
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_nat_add(v_size_1261_, v___x_1263_);
v___x_1265_ = lean_array_get_size(v_keyArray_1262_);
v___x_1266_ = lean_nat_dec_lt(v___x_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_dec(v___x_1264_);
lean_dec(v_index_1260_);
lean_dec_ref(v_toProcess_1255_);
lean_dec_ref(v_exprFVarArgs_1254_);
lean_dec_ref(v_exprMVarArgs_1253_);
lean_dec(v_nextExprIdx_1252_);
lean_dec_ref(v_newLetDecls_1251_);
lean_dec_ref(v_newLocalDeclsForMVars_1250_);
lean_dec_ref(v_newLocalDecls_1249_);
lean_dec_ref(v_levelArgs_1248_);
lean_dec(v_nextLevelIdx_1247_);
lean_dec_ref(v_levelParams_1246_);
lean_dec_ref(v_visitedExpr_1245_);
v___y_1225_ = v___x_1243_;
v___y_1226_ = v_a_1242_;
v___y_1227_ = v_visitedLevel_1244_;
goto v___jp_1224_;
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1267_ = lean_unsigned_to_nat(4u);
v___x_1268_ = lean_nat_mul(v___x_1264_, v___x_1267_);
v___x_1269_ = lean_unsigned_to_nat(3u);
v___x_1270_ = lean_nat_mul(v___x_1265_, v___x_1269_);
v___x_1271_ = lean_nat_dec_le(v___x_1268_, v___x_1270_);
lean_dec(v___x_1270_);
lean_dec(v___x_1268_);
if (v___x_1271_ == 0)
{
lean_dec(v___x_1264_);
lean_dec(v_index_1260_);
lean_dec_ref(v_toProcess_1255_);
lean_dec_ref(v_exprFVarArgs_1254_);
lean_dec_ref(v_exprMVarArgs_1253_);
lean_dec(v_nextExprIdx_1252_);
lean_dec_ref(v_newLetDecls_1251_);
lean_dec_ref(v_newLocalDeclsForMVars_1250_);
lean_dec_ref(v_newLocalDecls_1249_);
lean_dec_ref(v_levelArgs_1248_);
lean_dec(v_nextLevelIdx_1247_);
lean_dec_ref(v_levelParams_1246_);
lean_dec_ref(v_visitedExpr_1245_);
v___y_1225_ = v___x_1243_;
v___y_1226_ = v_a_1242_;
v___y_1227_ = v_visitedLevel_1244_;
goto v___jp_1224_;
}
else
{
lean_object* v___x_1272_; 
lean_dec(v___x_1243_);
lean_inc(v_a_1242_);
lean_inc(v_a_1016_);
v___x_1272_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_1244_, v___x_1264_, v_index_1260_, v_a_1016_, v_a_1242_);
lean_dec(v_index_1260_);
v_visitedExpr_1164_ = v_visitedExpr_1245_;
v_levelParams_1165_ = v_levelParams_1246_;
v_nextLevelIdx_1166_ = v_nextLevelIdx_1247_;
v_levelArgs_1167_ = v_levelArgs_1248_;
v_newLocalDecls_1168_ = v_newLocalDecls_1249_;
v_newLocalDeclsForMVars_1169_ = v_newLocalDeclsForMVars_1250_;
v_newLetDecls_1170_ = v_newLetDecls_1251_;
v_nextExprIdx_1171_ = v_nextExprIdx_1252_;
v_exprMVarArgs_1172_ = v_exprMVarArgs_1253_;
v_exprFVarArgs_1173_ = v_exprFVarArgs_1254_;
v_toProcess_1174_ = v_toProcess_1255_;
v___y_1175_ = v_a_1242_;
v___y_1176_ = v___x_1272_;
goto v___jp_1163_;
}
}
}
default: 
{
lean_object* v_size_1273_; lean_object* v_keyArray_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
lean_dec_ref(v_toProcess_1255_);
lean_dec_ref(v_exprFVarArgs_1254_);
lean_dec_ref(v_exprMVarArgs_1253_);
lean_dec(v_nextExprIdx_1252_);
lean_dec_ref(v_newLetDecls_1251_);
lean_dec_ref(v_newLocalDeclsForMVars_1250_);
lean_dec_ref(v_newLocalDecls_1249_);
lean_dec_ref(v_levelArgs_1248_);
lean_dec(v_nextLevelIdx_1247_);
lean_dec_ref(v_levelParams_1246_);
lean_dec_ref(v_visitedExpr_1245_);
v_size_1273_ = lean_ctor_get(v_visitedLevel_1244_, 0);
v_keyArray_1274_ = lean_ctor_get(v_visitedLevel_1244_, 1);
v___x_1275_ = lean_unsigned_to_nat(1u);
v___x_1276_ = lean_nat_add(v_size_1273_, v___x_1275_);
v___x_1277_ = lean_array_get_size(v_keyArray_1274_);
v___x_1278_ = lean_nat_dec_lt(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_dec(v___x_1276_);
v___x_1279_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_visitedLevel_1244_);
lean_dec_ref(v_visitedLevel_1244_);
v___y_1204_ = v___x_1243_;
v___y_1205_ = v_a_1242_;
v___y_1206_ = v___x_1279_;
goto v___jp_1203_;
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1280_ = lean_unsigned_to_nat(4u);
v___x_1281_ = lean_nat_mul(v___x_1276_, v___x_1280_);
lean_dec(v___x_1276_);
v___x_1282_ = lean_unsigned_to_nat(3u);
v___x_1283_ = lean_nat_mul(v___x_1277_, v___x_1282_);
v___x_1284_ = lean_nat_dec_le(v___x_1281_, v___x_1283_);
lean_dec(v___x_1283_);
lean_dec(v___x_1281_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_visitedLevel_1244_);
lean_dec_ref(v_visitedLevel_1244_);
v___y_1204_ = v___x_1243_;
v___y_1205_ = v_a_1242_;
v___y_1206_ = v___x_1285_;
goto v___jp_1203_;
}
else
{
v___y_1204_ = v___x_1243_;
v___y_1205_ = v_a_1242_;
v___y_1206_ = v_visitedLevel_1244_;
goto v___jp_1203_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1286_; 
v_a_1286_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1241_, 1);
v_a_1160_ = v_a_1286_;
goto v___jp_1159_;
}
else
{
lean_dec_ref_known(v_x_586_, 2);
return v___x_1241_;
}
}
}
else
{
lean_object* v_val_1287_; 
v_val_1287_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_val_1287_);
lean_dec_ref_known(v___x_1240_, 1);
v_a_1160_ = v_val_1287_;
goto v___jp_1159_;
}
}
}
default: 
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_x_586_, v_a_587_);
return v___x_1290_;
}
}
v___jp_589_:
{
if (v___y_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v_x_586_);
v___x_593_ = l_Lean_mkLevelMax_x27(v___y_590_, v___y_591_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = l_Lean_simpLevelMax_x27(v___y_590_, v___y_591_, v_x_586_);
lean_dec(v_x_586_);
lean_dec(v___y_591_);
lean_dec(v___y_590_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
v___jp_597_:
{
if (v___y_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_x_586_);
v___x_601_ = l_Lean_mkLevelIMax_x27(v___y_598_, v___y_599_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = l_Lean_simpLevelIMax_x27(v___y_598_, v___y_599_, v_x_586_);
lean_dec(v_x_586_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object* v_x_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_1291_, v_a_1292_);
lean_dec(v_a_1292_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* v_x_1295_, uint8_t v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_1295_, v_a_1297_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* v_x_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
uint8_t v_a_boxed_1312_; lean_object* v_res_1313_; 
v_a_boxed_1312_ = lean_unbox(v_a_1305_);
v_res_1313_ = l_Lean_Meta_Closure_collectLevelAux(v_x_1304_, v_a_boxed_1312_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(lean_object* v_00_u03b2_1314_, lean_object* v_m_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_1315_, v_a_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object* v_00_u03b2_1318_, lean_object* v_m_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(v_00_u03b2_1318_, v_m_1319_, v_a_1320_);
lean_dec(v_a_1320_);
lean_dec_ref(v_m_1319_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2(lean_object* v_00_u03b2_1322_, lean_object* v_m_1323_, lean_object* v_query_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_m_1323_, v_query_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___boxed(lean_object* v_00_u03b2_1326_, lean_object* v_m_1327_, lean_object* v_query_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2(v_00_u03b2_1326_, v_m_1327_, v_query_1328_);
lean_dec(v_query_1328_);
lean_dec_ref(v_m_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3(lean_object* v_00_u03b2_1330_, lean_object* v_m_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_m_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___boxed(lean_object* v_00_u03b2_1333_, lean_object* v_m_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3(v_00_u03b2_1333_, v_m_1334_);
lean_dec_ref(v_m_1334_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(lean_object* v_00_u03b2_1336_, lean_object* v_m_1337_, lean_object* v_query_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_m_1337_, v_query_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1340_, lean_object* v_m_1341_, lean_object* v_query_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(v_00_u03b2_1340_, v_m_1341_, v_query_1342_);
lean_dec(v_query_1342_);
lean_dec_ref(v_m_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(lean_object* v_00_u03b2_1344_, lean_object* v_m_1345_, lean_object* v_query_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_m_1345_, v_query_1346_, v_x_1347_, v_x_1348_, v_x_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1352_, lean_object* v_m_1353_, lean_object* v_query_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(v_00_u03b2_1352_, v_m_1353_, v_query_1354_, v_x_1355_, v_x_1356_, v_x_1357_, v_x_1358_);
lean_dec(v_query_1354_);
lean_dec_ref(v_m_1353_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5(lean_object* v_00_u03b2_1360_, lean_object* v_init_1361_, lean_object* v_b_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5___redArg(v_init_1361_, v_b_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1364_, lean_object* v_init_1365_, lean_object* v_b_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5(v_00_u03b2_1364_, v_init_1365_, v_b_1366_);
lean_dec_ref(v_b_1366_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1368_, lean_object* v_b_1369_, lean_object* v_acc_1370_, lean_object* v_i_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5_spec__6___redArg(v_b_1369_, v_acc_1370_, v_i_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1373_, lean_object* v_b_1374_, lean_object* v_acc_1375_, lean_object* v_i_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3_spec__5_spec__6(v_00_u03b2_1373_, v_b_1374_, v_acc_1375_, v_i_1376_);
lean_dec_ref(v_b_1374_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object* v_u_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_visitedExpr_1382_; lean_object* v_levelParams_1383_; lean_object* v_nextLevelIdx_1384_; lean_object* v_levelArgs_1385_; lean_object* v_newLocalDecls_1386_; lean_object* v_newLocalDeclsForMVars_1387_; lean_object* v_newLetDecls_1388_; lean_object* v_nextExprIdx_1389_; lean_object* v_exprMVarArgs_1390_; lean_object* v_exprFVarArgs_1391_; lean_object* v_toProcess_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v_i_1417_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v_i_1438_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; uint8_t v___x_1513_; 
v___x_1513_ = l_Lean_Level_hasMVar(v_u_1378_);
if (v___x_1513_ == 0)
{
uint8_t v___x_1514_; 
v___x_1514_ = l_Lean_Level_hasParam(v_u_1378_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v_u_1378_);
return v___x_1515_;
}
else
{
goto v___jp_1456_;
}
}
else
{
goto v___jp_1456_;
}
v___jp_1381_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1395_, 0, v___y_1394_);
lean_ctor_set(v___x_1395_, 1, v_visitedExpr_1382_);
lean_ctor_set(v___x_1395_, 2, v_levelParams_1383_);
lean_ctor_set(v___x_1395_, 3, v_nextLevelIdx_1384_);
lean_ctor_set(v___x_1395_, 4, v_levelArgs_1385_);
lean_ctor_set(v___x_1395_, 5, v_newLocalDecls_1386_);
lean_ctor_set(v___x_1395_, 6, v_newLocalDeclsForMVars_1387_);
lean_ctor_set(v___x_1395_, 7, v_newLetDecls_1388_);
lean_ctor_set(v___x_1395_, 8, v_nextExprIdx_1389_);
lean_ctor_set(v___x_1395_, 9, v_exprMVarArgs_1390_);
lean_ctor_set(v___x_1395_, 10, v_exprFVarArgs_1391_);
lean_ctor_set(v___x_1395_, 11, v_toProcess_1392_);
v___x_1396_ = lean_st_ref_put(v_a_1379_, v___x_1395_);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___y_1393_);
return v___x_1397_;
}
v___jp_1398_:
{
lean_object* v_visitedExpr_1402_; lean_object* v_levelParams_1403_; lean_object* v_nextLevelIdx_1404_; lean_object* v_levelArgs_1405_; lean_object* v_newLocalDecls_1406_; lean_object* v_newLocalDeclsForMVars_1407_; lean_object* v_newLetDecls_1408_; lean_object* v_nextExprIdx_1409_; lean_object* v_exprMVarArgs_1410_; lean_object* v_exprFVarArgs_1411_; lean_object* v_toProcess_1412_; 
v_visitedExpr_1402_ = lean_ctor_get(v___y_1399_, 1);
lean_inc_ref(v_visitedExpr_1402_);
v_levelParams_1403_ = lean_ctor_get(v___y_1399_, 2);
lean_inc_ref(v_levelParams_1403_);
v_nextLevelIdx_1404_ = lean_ctor_get(v___y_1399_, 3);
lean_inc(v_nextLevelIdx_1404_);
v_levelArgs_1405_ = lean_ctor_get(v___y_1399_, 4);
lean_inc_ref(v_levelArgs_1405_);
v_newLocalDecls_1406_ = lean_ctor_get(v___y_1399_, 5);
lean_inc_ref(v_newLocalDecls_1406_);
v_newLocalDeclsForMVars_1407_ = lean_ctor_get(v___y_1399_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_1407_);
v_newLetDecls_1408_ = lean_ctor_get(v___y_1399_, 7);
lean_inc_ref(v_newLetDecls_1408_);
v_nextExprIdx_1409_ = lean_ctor_get(v___y_1399_, 8);
lean_inc(v_nextExprIdx_1409_);
v_exprMVarArgs_1410_ = lean_ctor_get(v___y_1399_, 9);
lean_inc_ref(v_exprMVarArgs_1410_);
v_exprFVarArgs_1411_ = lean_ctor_get(v___y_1399_, 10);
lean_inc_ref(v_exprFVarArgs_1411_);
v_toProcess_1412_ = lean_ctor_get(v___y_1399_, 11);
lean_inc_ref(v_toProcess_1412_);
lean_dec_ref(v___y_1399_);
v_visitedExpr_1382_ = v_visitedExpr_1402_;
v_levelParams_1383_ = v_levelParams_1403_;
v_nextLevelIdx_1384_ = v_nextLevelIdx_1404_;
v_levelArgs_1385_ = v_levelArgs_1405_;
v_newLocalDecls_1386_ = v_newLocalDecls_1406_;
v_newLocalDeclsForMVars_1387_ = v_newLocalDeclsForMVars_1407_;
v_newLetDecls_1388_ = v_newLetDecls_1408_;
v_nextExprIdx_1389_ = v_nextExprIdx_1409_;
v_exprMVarArgs_1390_ = v_exprMVarArgs_1410_;
v_exprFVarArgs_1391_ = v_exprFVarArgs_1411_;
v_toProcess_1392_ = v_toProcess_1412_;
v___y_1393_ = v___y_1400_;
v___y_1394_ = v___y_1401_;
goto v___jp_1381_;
}
v___jp_1413_:
{
lean_object* v_size_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_size_1418_ = lean_ctor_get(v___y_1416_, 0);
v___x_1419_ = lean_unsigned_to_nat(1u);
v___x_1420_ = lean_nat_add(v_size_1418_, v___x_1419_);
lean_inc(v___y_1415_);
v___x_1421_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1416_, v___x_1420_, v_i_1417_, v_u_1378_, v___y_1415_);
lean_dec(v_i_1417_);
v___y_1399_ = v___y_1414_;
v___y_1400_ = v___y_1415_;
v___y_1401_ = v___x_1421_;
goto v___jp_1398_;
}
v___jp_1422_:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v___y_1425_, v_u_1378_);
switch(lean_obj_tag(v___x_1426_))
{
case 0:
{
lean_object* v_index_1427_; lean_object* v_size_1428_; lean_object* v___x_1429_; 
v_index_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_index_1427_);
lean_dec_ref_known(v___x_1426_, 3);
v_size_1428_ = lean_ctor_get(v___y_1425_, 0);
lean_inc(v_size_1428_);
lean_inc(v___y_1424_);
v___x_1429_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1425_, v_size_1428_, v_index_1427_, v_u_1378_, v___y_1424_);
lean_dec(v_index_1427_);
v___y_1399_ = v___y_1423_;
v___y_1400_ = v___y_1424_;
v___y_1401_ = v___x_1429_;
goto v___jp_1398_;
}
case 1:
{
lean_object* v_index_1430_; 
v_index_1430_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_index_1430_);
lean_dec_ref_known(v___x_1426_, 1);
v___y_1414_ = v___y_1423_;
v___y_1415_ = v___y_1424_;
v___y_1416_ = v___y_1425_;
v_i_1417_ = v_index_1430_;
goto v___jp_1413_;
}
default: 
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1425_, v___x_1431_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_index_1433_; 
v_index_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_index_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v___y_1414_ = v___y_1423_;
v___y_1415_ = v___y_1424_;
v___y_1416_ = v___y_1425_;
v_i_1417_ = v_index_1433_;
goto v___jp_1413_;
}
else
{
lean_dec(v_u_1378_);
v___y_1399_ = v___y_1423_;
v___y_1400_ = v___y_1424_;
v___y_1401_ = v___y_1425_;
goto v___jp_1398_;
}
}
}
}
v___jp_1434_:
{
lean_object* v_size_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_size_1439_ = lean_ctor_get(v___y_1437_, 0);
v___x_1440_ = lean_unsigned_to_nat(1u);
v___x_1441_ = lean_nat_add(v_size_1439_, v___x_1440_);
lean_inc(v___y_1436_);
v___x_1442_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1437_, v___x_1441_, v_i_1438_, v_u_1378_, v___y_1436_);
lean_dec(v_i_1438_);
v___y_1399_ = v___y_1435_;
v___y_1400_ = v___y_1436_;
v___y_1401_ = v___x_1442_;
goto v___jp_1398_;
}
v___jp_1443_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v___y_1446_);
lean_dec_ref(v___y_1446_);
v___x_1448_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v___x_1447_, v_u_1378_);
switch(lean_obj_tag(v___x_1448_))
{
case 0:
{
lean_object* v_index_1449_; lean_object* v_size_1450_; lean_object* v___x_1451_; 
v_index_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_index_1449_);
lean_dec_ref_known(v___x_1448_, 3);
v_size_1450_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_size_1450_);
lean_inc(v___y_1445_);
v___x_1451_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1447_, v_size_1450_, v_index_1449_, v_u_1378_, v___y_1445_);
lean_dec(v_index_1449_);
v___y_1399_ = v___y_1444_;
v___y_1400_ = v___y_1445_;
v___y_1401_ = v___x_1451_;
goto v___jp_1398_;
}
case 1:
{
lean_object* v_index_1452_; 
v_index_1452_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_index_1452_);
lean_dec_ref_known(v___x_1448_, 1);
v___y_1435_ = v___y_1444_;
v___y_1436_ = v___y_1445_;
v___y_1437_ = v___x_1447_;
v_i_1438_ = v_index_1452_;
goto v___jp_1434_;
}
default: 
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1447_, v___x_1453_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_index_1455_; 
v_index_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_index_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v___y_1435_ = v___y_1444_;
v___y_1436_ = v___y_1445_;
v___y_1437_ = v___x_1447_;
v_i_1438_ = v_index_1455_;
goto v___jp_1434_;
}
else
{
lean_dec(v_u_1378_);
v___y_1399_ = v___y_1444_;
v___y_1400_ = v___y_1445_;
v___y_1401_ = v___x_1447_;
goto v___jp_1398_;
}
}
}
}
v___jp_1456_:
{
lean_object* v___x_1457_; lean_object* v_visitedLevel_1458_; lean_object* v___x_1459_; 
v___x_1457_ = lean_st_ref_get(v_a_1379_);
v_visitedLevel_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc_ref(v_visitedLevel_1458_);
lean_dec(v___x_1457_);
v___x_1459_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_1458_, v_u_1378_);
lean_dec_ref(v_visitedLevel_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v___x_1460_; 
lean_inc(v_u_1378_);
v___x_1460_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_u_1378_, v_a_1379_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; lean_object* v_visitedLevel_1463_; lean_object* v_visitedExpr_1464_; lean_object* v_levelParams_1465_; lean_object* v_nextLevelIdx_1466_; lean_object* v_levelArgs_1467_; lean_object* v_newLocalDecls_1468_; lean_object* v_newLocalDeclsForMVars_1469_; lean_object* v_newLetDecls_1470_; lean_object* v_nextExprIdx_1471_; lean_object* v_exprMVarArgs_1472_; lean_object* v_exprFVarArgs_1473_; lean_object* v_toProcess_1474_; lean_object* v___x_1475_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = lean_st_ref_take(v_a_1379_);
v_visitedLevel_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc_ref(v_visitedLevel_1463_);
v_visitedExpr_1464_ = lean_ctor_get(v___x_1462_, 1);
lean_inc_ref(v_visitedExpr_1464_);
v_levelParams_1465_ = lean_ctor_get(v___x_1462_, 2);
lean_inc_ref(v_levelParams_1465_);
v_nextLevelIdx_1466_ = lean_ctor_get(v___x_1462_, 3);
lean_inc(v_nextLevelIdx_1466_);
v_levelArgs_1467_ = lean_ctor_get(v___x_1462_, 4);
lean_inc_ref(v_levelArgs_1467_);
v_newLocalDecls_1468_ = lean_ctor_get(v___x_1462_, 5);
lean_inc_ref(v_newLocalDecls_1468_);
v_newLocalDeclsForMVars_1469_ = lean_ctor_get(v___x_1462_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_1469_);
v_newLetDecls_1470_ = lean_ctor_get(v___x_1462_, 7);
lean_inc_ref(v_newLetDecls_1470_);
v_nextExprIdx_1471_ = lean_ctor_get(v___x_1462_, 8);
lean_inc(v_nextExprIdx_1471_);
v_exprMVarArgs_1472_ = lean_ctor_get(v___x_1462_, 9);
lean_inc_ref(v_exprMVarArgs_1472_);
v_exprFVarArgs_1473_ = lean_ctor_get(v___x_1462_, 10);
lean_inc_ref(v_exprFVarArgs_1473_);
v_toProcess_1474_ = lean_ctor_get(v___x_1462_, 11);
lean_inc_ref(v_toProcess_1474_);
v___x_1475_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_1463_, v_u_1378_);
switch(lean_obj_tag(v___x_1475_))
{
case 0:
{
lean_object* v_index_1476_; lean_object* v_size_1477_; lean_object* v___x_1478_; 
lean_dec(v___x_1462_);
v_index_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_index_1476_);
lean_dec_ref_known(v___x_1475_, 3);
v_size_1477_ = lean_ctor_get(v_visitedLevel_1463_, 0);
lean_inc(v_size_1477_);
lean_inc(v_a_1461_);
v___x_1478_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_1463_, v_size_1477_, v_index_1476_, v_u_1378_, v_a_1461_);
lean_dec(v_index_1476_);
v_visitedExpr_1382_ = v_visitedExpr_1464_;
v_levelParams_1383_ = v_levelParams_1465_;
v_nextLevelIdx_1384_ = v_nextLevelIdx_1466_;
v_levelArgs_1385_ = v_levelArgs_1467_;
v_newLocalDecls_1386_ = v_newLocalDecls_1468_;
v_newLocalDeclsForMVars_1387_ = v_newLocalDeclsForMVars_1469_;
v_newLetDecls_1388_ = v_newLetDecls_1470_;
v_nextExprIdx_1389_ = v_nextExprIdx_1471_;
v_exprMVarArgs_1390_ = v_exprMVarArgs_1472_;
v_exprFVarArgs_1391_ = v_exprFVarArgs_1473_;
v_toProcess_1392_ = v_toProcess_1474_;
v___y_1393_ = v_a_1461_;
v___y_1394_ = v___x_1478_;
goto v___jp_1381_;
}
case 1:
{
lean_object* v_index_1479_; lean_object* v_size_1480_; lean_object* v_keyArray_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v_index_1479_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_index_1479_);
lean_dec_ref_known(v___x_1475_, 1);
v_size_1480_ = lean_ctor_get(v_visitedLevel_1463_, 0);
v_keyArray_1481_ = lean_ctor_get(v_visitedLevel_1463_, 1);
v___x_1482_ = lean_unsigned_to_nat(1u);
v___x_1483_ = lean_nat_add(v_size_1480_, v___x_1482_);
v___x_1484_ = lean_array_get_size(v_keyArray_1481_);
v___x_1485_ = lean_nat_dec_lt(v___x_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_dec(v___x_1483_);
lean_dec(v_index_1479_);
lean_dec_ref(v_toProcess_1474_);
lean_dec_ref(v_exprFVarArgs_1473_);
lean_dec_ref(v_exprMVarArgs_1472_);
lean_dec(v_nextExprIdx_1471_);
lean_dec_ref(v_newLetDecls_1470_);
lean_dec_ref(v_newLocalDeclsForMVars_1469_);
lean_dec_ref(v_newLocalDecls_1468_);
lean_dec_ref(v_levelArgs_1467_);
lean_dec(v_nextLevelIdx_1466_);
lean_dec_ref(v_levelParams_1465_);
lean_dec_ref(v_visitedExpr_1464_);
v___y_1444_ = v___x_1462_;
v___y_1445_ = v_a_1461_;
v___y_1446_ = v_visitedLevel_1463_;
goto v___jp_1443_;
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1486_ = lean_unsigned_to_nat(4u);
v___x_1487_ = lean_nat_mul(v___x_1483_, v___x_1486_);
v___x_1488_ = lean_unsigned_to_nat(3u);
v___x_1489_ = lean_nat_mul(v___x_1484_, v___x_1488_);
v___x_1490_ = lean_nat_dec_le(v___x_1487_, v___x_1489_);
lean_dec(v___x_1489_);
lean_dec(v___x_1487_);
if (v___x_1490_ == 0)
{
lean_dec(v___x_1483_);
lean_dec(v_index_1479_);
lean_dec_ref(v_toProcess_1474_);
lean_dec_ref(v_exprFVarArgs_1473_);
lean_dec_ref(v_exprMVarArgs_1472_);
lean_dec(v_nextExprIdx_1471_);
lean_dec_ref(v_newLetDecls_1470_);
lean_dec_ref(v_newLocalDeclsForMVars_1469_);
lean_dec_ref(v_newLocalDecls_1468_);
lean_dec_ref(v_levelArgs_1467_);
lean_dec(v_nextLevelIdx_1466_);
lean_dec_ref(v_levelParams_1465_);
lean_dec_ref(v_visitedExpr_1464_);
v___y_1444_ = v___x_1462_;
v___y_1445_ = v_a_1461_;
v___y_1446_ = v_visitedLevel_1463_;
goto v___jp_1443_;
}
else
{
lean_object* v___x_1491_; 
lean_dec(v___x_1462_);
lean_inc(v_a_1461_);
v___x_1491_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_1463_, v___x_1483_, v_index_1479_, v_u_1378_, v_a_1461_);
lean_dec(v_index_1479_);
v_visitedExpr_1382_ = v_visitedExpr_1464_;
v_levelParams_1383_ = v_levelParams_1465_;
v_nextLevelIdx_1384_ = v_nextLevelIdx_1466_;
v_levelArgs_1385_ = v_levelArgs_1467_;
v_newLocalDecls_1386_ = v_newLocalDecls_1468_;
v_newLocalDeclsForMVars_1387_ = v_newLocalDeclsForMVars_1469_;
v_newLetDecls_1388_ = v_newLetDecls_1470_;
v_nextExprIdx_1389_ = v_nextExprIdx_1471_;
v_exprMVarArgs_1390_ = v_exprMVarArgs_1472_;
v_exprFVarArgs_1391_ = v_exprFVarArgs_1473_;
v_toProcess_1392_ = v_toProcess_1474_;
v___y_1393_ = v_a_1461_;
v___y_1394_ = v___x_1491_;
goto v___jp_1381_;
}
}
}
default: 
{
lean_object* v_size_1492_; lean_object* v_keyArray_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
lean_dec_ref(v_toProcess_1474_);
lean_dec_ref(v_exprFVarArgs_1473_);
lean_dec_ref(v_exprMVarArgs_1472_);
lean_dec(v_nextExprIdx_1471_);
lean_dec_ref(v_newLetDecls_1470_);
lean_dec_ref(v_newLocalDeclsForMVars_1469_);
lean_dec_ref(v_newLocalDecls_1468_);
lean_dec_ref(v_levelArgs_1467_);
lean_dec(v_nextLevelIdx_1466_);
lean_dec_ref(v_levelParams_1465_);
lean_dec_ref(v_visitedExpr_1464_);
v_size_1492_ = lean_ctor_get(v_visitedLevel_1463_, 0);
v_keyArray_1493_ = lean_ctor_get(v_visitedLevel_1463_, 1);
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_nat_add(v_size_1492_, v___x_1494_);
v___x_1496_ = lean_array_get_size(v_keyArray_1493_);
v___x_1497_ = lean_nat_dec_lt(v___x_1495_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; 
lean_dec(v___x_1495_);
v___x_1498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_visitedLevel_1463_);
lean_dec_ref(v_visitedLevel_1463_);
v___y_1423_ = v___x_1462_;
v___y_1424_ = v_a_1461_;
v___y_1425_ = v___x_1498_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1499_ = lean_unsigned_to_nat(4u);
v___x_1500_ = lean_nat_mul(v___x_1495_, v___x_1499_);
lean_dec(v___x_1495_);
v___x_1501_ = lean_unsigned_to_nat(3u);
v___x_1502_ = lean_nat_mul(v___x_1496_, v___x_1501_);
v___x_1503_ = lean_nat_dec_le(v___x_1500_, v___x_1502_);
lean_dec(v___x_1502_);
lean_dec(v___x_1500_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectLevelAux_spec__3___redArg(v_visitedLevel_1463_);
lean_dec_ref(v_visitedLevel_1463_);
v___y_1423_ = v___x_1462_;
v___y_1424_ = v_a_1461_;
v___y_1425_ = v___x_1504_;
goto v___jp_1422_;
}
else
{
v___y_1423_ = v___x_1462_;
v___y_1424_ = v_a_1461_;
v___y_1425_ = v_visitedLevel_1463_;
goto v___jp_1422_;
}
}
}
}
}
else
{
lean_dec(v_u_1378_);
return v___x_1460_;
}
}
else
{
lean_object* v_val_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_u_1378_);
v_val_1505_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1459_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_val_1505_);
lean_dec(v___x_1459_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set_tag(v___x_1507_, 0);
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_val_1505_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg___boxed(lean_object* v_u_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_1516_, v_a_1517_);
lean_dec(v_a_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* v_u_1520_, uint8_t v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_1520_, v_a_1522_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* v_u_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
uint8_t v_a_boxed_1537_; lean_object* v_res_1538_; 
v_a_boxed_1537_ = lean_unbox(v_a_1530_);
v_res_1538_ = l_Lean_Meta_Closure_collectLevel(v_u_1529_, v_a_boxed_1537_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object* v_e_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v___x_1542_; 
v___x_1542_ = l_Lean_Expr_hasMVar(v_e_1539_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_e_1539_);
return v___x_1543_;
}
else
{
lean_object* v___x_1544_; lean_object* v_mctx_1545_; lean_object* v___x_1546_; lean_object* v_fst_1547_; lean_object* v_snd_1548_; lean_object* v___x_1549_; lean_object* v_cache_1550_; lean_object* v_zetaDeltaFVarIds_1551_; lean_object* v_postponed_1552_; lean_object* v_diag_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1562_; 
v___x_1544_ = lean_st_ref_get(v___y_1540_);
v_mctx_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc_ref(v_mctx_1545_);
lean_dec(v___x_1544_);
v___x_1546_ = l_Lean_instantiateMVarsCore(v_mctx_1545_, v_e_1539_);
v_fst_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_fst_1547_);
v_snd_1548_ = lean_ctor_get(v___x_1546_, 1);
lean_inc(v_snd_1548_);
lean_dec_ref(v___x_1546_);
v___x_1549_ = lean_st_ref_take(v___y_1540_);
v_cache_1550_ = lean_ctor_get(v___x_1549_, 1);
v_zetaDeltaFVarIds_1551_ = lean_ctor_get(v___x_1549_, 2);
v_postponed_1552_ = lean_ctor_get(v___x_1549_, 3);
v_diag_1553_ = lean_ctor_get(v___x_1549_, 4);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v___x_1549_, 0);
lean_dec(v_unused_1563_);
v___x_1555_ = v___x_1549_;
v_isShared_1556_ = v_isSharedCheck_1562_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_diag_1553_);
lean_inc(v_postponed_1552_);
lean_inc(v_zetaDeltaFVarIds_1551_);
lean_inc(v_cache_1550_);
lean_dec(v___x_1549_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1562_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v_snd_1548_);
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_snd_1548_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_cache_1550_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_zetaDeltaFVarIds_1551_);
lean_ctor_set(v_reuseFailAlloc_1561_, 3, v_postponed_1552_);
lean_ctor_set(v_reuseFailAlloc_1561_, 4, v_diag_1553_);
v___x_1558_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_st_ref_put(v___y_1540_, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v_fst_1547_);
return v___x_1560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object* v_e_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_1564_, v___y_1565_);
lean_dec(v___y_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(lean_object* v_e_1568_, uint8_t v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_1568_, v___y_1572_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object* v_e_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
uint8_t v___y_2268__boxed_1585_; lean_object* v_res_1586_; 
v___y_2268__boxed_1585_ = lean_unbox(v___y_1578_);
v_res_1586_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(v_e_1577_, v___y_2268__boxed_1585_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object* v_e_1587_, uint8_t v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_1587_, v_a_1591_);
if (v_a_1588_ == 0)
{
lean_object* v_a_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc_n(v_a_1596_, 2);
lean_dec_ref(v___x_1595_);
v___x_1597_ = 0;
v___x_1598_ = l_Lean_Meta_check(v_a_1596_, v___x_1597_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v___x_1598_, 0);
lean_dec(v_unused_1606_);
v___x_1600_ = v___x_1598_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_dec(v___x_1598_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_a_1596_);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1596_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v_a_1596_);
v_a_1607_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1598_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1598_);
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
}
else
{
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* v_e_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
uint8_t v_a_boxed_1623_; lean_object* v_res_1624_; 
v_a_boxed_1623_ = lean_unbox(v_a_1616_);
v_res_1624_ = l_Lean_Meta_Closure_preprocess(v_e_1615_, v_a_boxed_1623_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object* v_a_1628_){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v_visitedLevel_1632_; lean_object* v_visitedExpr_1633_; lean_object* v_levelParams_1634_; lean_object* v_nextLevelIdx_1635_; lean_object* v_levelArgs_1636_; lean_object* v_newLocalDecls_1637_; lean_object* v_newLocalDeclsForMVars_1638_; lean_object* v_newLetDecls_1639_; lean_object* v_nextExprIdx_1640_; lean_object* v_exprMVarArgs_1641_; lean_object* v_exprFVarArgs_1642_; lean_object* v_toProcess_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1657_; 
v___x_1630_ = lean_st_ref_get(v_a_1628_);
v___x_1631_ = lean_st_ref_take(v_a_1628_);
v_visitedLevel_1632_ = lean_ctor_get(v___x_1631_, 0);
v_visitedExpr_1633_ = lean_ctor_get(v___x_1631_, 1);
v_levelParams_1634_ = lean_ctor_get(v___x_1631_, 2);
v_nextLevelIdx_1635_ = lean_ctor_get(v___x_1631_, 3);
v_levelArgs_1636_ = lean_ctor_get(v___x_1631_, 4);
v_newLocalDecls_1637_ = lean_ctor_get(v___x_1631_, 5);
v_newLocalDeclsForMVars_1638_ = lean_ctor_get(v___x_1631_, 6);
v_newLetDecls_1639_ = lean_ctor_get(v___x_1631_, 7);
v_nextExprIdx_1640_ = lean_ctor_get(v___x_1631_, 8);
v_exprMVarArgs_1641_ = lean_ctor_get(v___x_1631_, 9);
v_exprFVarArgs_1642_ = lean_ctor_get(v___x_1631_, 10);
v_toProcess_1643_ = lean_ctor_get(v___x_1631_, 11);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1645_ = v___x_1631_;
v_isShared_1646_ = v_isSharedCheck_1657_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_toProcess_1643_);
lean_inc(v_exprFVarArgs_1642_);
lean_inc(v_exprMVarArgs_1641_);
lean_inc(v_nextExprIdx_1640_);
lean_inc(v_newLetDecls_1639_);
lean_inc(v_newLocalDeclsForMVars_1638_);
lean_inc(v_newLocalDecls_1637_);
lean_inc(v_levelArgs_1636_);
lean_inc(v_nextLevelIdx_1635_);
lean_inc(v_levelParams_1634_);
lean_inc(v_visitedExpr_1633_);
lean_inc(v_visitedLevel_1632_);
lean_dec(v___x_1631_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1657_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = lean_nat_add(v_nextExprIdx_1640_, v___x_1647_);
lean_dec(v_nextExprIdx_1640_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 8, v___x_1648_);
v___x_1650_ = v___x_1645_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_visitedLevel_1632_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_visitedExpr_1633_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_levelParams_1634_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v_nextLevelIdx_1635_);
lean_ctor_set(v_reuseFailAlloc_1656_, 4, v_levelArgs_1636_);
lean_ctor_set(v_reuseFailAlloc_1656_, 5, v_newLocalDecls_1637_);
lean_ctor_set(v_reuseFailAlloc_1656_, 6, v_newLocalDeclsForMVars_1638_);
lean_ctor_set(v_reuseFailAlloc_1656_, 7, v_newLetDecls_1639_);
lean_ctor_set(v_reuseFailAlloc_1656_, 8, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1656_, 9, v_exprMVarArgs_1641_);
lean_ctor_set(v_reuseFailAlloc_1656_, 10, v_exprFVarArgs_1642_);
lean_ctor_set(v_reuseFailAlloc_1656_, 11, v_toProcess_1643_);
v___x_1650_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1651_; lean_object* v_nextExprIdx_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1651_ = lean_st_ref_put(v_a_1628_, v___x_1650_);
v_nextExprIdx_1652_ = lean_ctor_get(v___x_1630_, 8);
lean_inc(v_nextExprIdx_1652_);
lean_dec(v___x_1630_);
v___x_1653_ = ((lean_object*)(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1));
v___x_1654_ = lean_name_append_index_after(v___x_1653_, v_nextExprIdx_1652_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_1658_);
lean_dec(v_a_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_1662_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
uint8_t v_a_boxed_1676_; lean_object* v_res_1677_; 
v_a_boxed_1676_ = lean_unbox(v_a_1669_);
v_res_1677_ = l_Lean_Meta_Closure_mkNextUserName(v_a_boxed_1676_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object* v_elem_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v_visitedLevel_1682_; lean_object* v_visitedExpr_1683_; lean_object* v_levelParams_1684_; lean_object* v_nextLevelIdx_1685_; lean_object* v_levelArgs_1686_; lean_object* v_newLocalDecls_1687_; lean_object* v_newLocalDeclsForMVars_1688_; lean_object* v_newLetDecls_1689_; lean_object* v_nextExprIdx_1690_; lean_object* v_exprMVarArgs_1691_; lean_object* v_exprFVarArgs_1692_; lean_object* v_toProcess_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1704_; 
v___x_1681_ = lean_st_ref_take(v_a_1679_);
v_visitedLevel_1682_ = lean_ctor_get(v___x_1681_, 0);
v_visitedExpr_1683_ = lean_ctor_get(v___x_1681_, 1);
v_levelParams_1684_ = lean_ctor_get(v___x_1681_, 2);
v_nextLevelIdx_1685_ = lean_ctor_get(v___x_1681_, 3);
v_levelArgs_1686_ = lean_ctor_get(v___x_1681_, 4);
v_newLocalDecls_1687_ = lean_ctor_get(v___x_1681_, 5);
v_newLocalDeclsForMVars_1688_ = lean_ctor_get(v___x_1681_, 6);
v_newLetDecls_1689_ = lean_ctor_get(v___x_1681_, 7);
v_nextExprIdx_1690_ = lean_ctor_get(v___x_1681_, 8);
v_exprMVarArgs_1691_ = lean_ctor_get(v___x_1681_, 9);
v_exprFVarArgs_1692_ = lean_ctor_get(v___x_1681_, 10);
v_toProcess_1693_ = lean_ctor_get(v___x_1681_, 11);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1695_ = v___x_1681_;
v_isShared_1696_ = v_isSharedCheck_1704_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_toProcess_1693_);
lean_inc(v_exprFVarArgs_1692_);
lean_inc(v_exprMVarArgs_1691_);
lean_inc(v_nextExprIdx_1690_);
lean_inc(v_newLetDecls_1689_);
lean_inc(v_newLocalDeclsForMVars_1688_);
lean_inc(v_newLocalDecls_1687_);
lean_inc(v_levelArgs_1686_);
lean_inc(v_nextLevelIdx_1685_);
lean_inc(v_levelParams_1684_);
lean_inc(v_visitedExpr_1683_);
lean_inc(v_visitedLevel_1682_);
lean_dec(v___x_1681_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1704_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = lean_array_push(v_toProcess_1693_, v_elem_1678_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 11, v___x_1697_);
v___x_1699_ = v___x_1695_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_visitedLevel_1682_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_visitedExpr_1683_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_levelParams_1684_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v_nextLevelIdx_1685_);
lean_ctor_set(v_reuseFailAlloc_1703_, 4, v_levelArgs_1686_);
lean_ctor_set(v_reuseFailAlloc_1703_, 5, v_newLocalDecls_1687_);
lean_ctor_set(v_reuseFailAlloc_1703_, 6, v_newLocalDeclsForMVars_1688_);
lean_ctor_set(v_reuseFailAlloc_1703_, 7, v_newLetDecls_1689_);
lean_ctor_set(v_reuseFailAlloc_1703_, 8, v_nextExprIdx_1690_);
lean_ctor_set(v_reuseFailAlloc_1703_, 9, v_exprMVarArgs_1691_);
lean_ctor_set(v_reuseFailAlloc_1703_, 10, v_exprFVarArgs_1692_);
lean_ctor_set(v_reuseFailAlloc_1703_, 11, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1700_ = lean_st_ref_put(v_a_1679_, v___x_1699_);
v___x_1701_ = lean_box(0);
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
return v___x_1702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object* v_elem_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_1705_, v_a_1706_);
lean_dec(v_a_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* v_elem_1709_, uint8_t v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_1709_, v_a_1711_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* v_elem_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
uint8_t v_a_boxed_1726_; lean_object* v_res_1727_; 
v_a_boxed_1726_ = lean_unbox(v_a_1719_);
v_res_1727_ = l_Lean_Meta_Closure_pushToProcess(v_elem_1718_, v_a_boxed_1726_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object* v_mvarId_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; lean_object* v_mctx_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1731_ = lean_st_ref_get(v___y_1729_);
v_mctx_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc_ref(v_mctx_1732_);
lean_dec(v___x_1731_);
v___x_1733_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_1732_, v_mvarId_1728_);
lean_dec_ref(v_mctx_1732_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(lean_object* v_mvarId_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_mvarId_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec(v_mvarId_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_object* v_mvarId_1739_, uint8_t v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_mvarId_1739_, v___y_1743_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(lean_object* v_mvarId_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
uint8_t v___y_18261__boxed_1756_; lean_object* v_res_1757_; 
v___y_18261__boxed_1756_ = lean_unbox(v___y_1749_);
v_res_1757_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__5(v_mvarId_1748_, v___y_18261__boxed_1756_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec(v_mvarId_1748_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg___lam__0(lean_object* v_k_1758_, uint8_t v___y_1759_, lean_object* v___y_1760_, lean_object* v_b_1761_, lean_object* v_c_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_box(v___y_1759_);
lean_inc(v___y_1766_);
lean_inc_ref(v___y_1765_);
lean_inc(v___y_1764_);
lean_inc_ref(v___y_1763_);
lean_inc(v___y_1760_);
v___x_1769_ = lean_apply_9(v_k_1758_, v_b_1761_, v_c_1762_, v___x_1768_, v___y_1760_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, lean_box(0));
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg___lam__0___boxed(lean_object* v_k_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v_b_1773_, lean_object* v_c_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
uint8_t v___y_18284__boxed_1780_; lean_object* v_res_1781_; 
v___y_18284__boxed_1780_ = lean_unbox(v___y_1771_);
v_res_1781_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg___lam__0(v_k_1770_, v___y_18284__boxed_1780_, v___y_1772_, v_b_1773_, v_c_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1772_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg(lean_object* v_type_1782_, lean_object* v_maxFVars_x3f_1783_, lean_object* v_k_1784_, uint8_t v_cleanupAnnotations_1785_, uint8_t v_whnfType_1786_, uint8_t v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; lean_object* v___f_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_box(v___y_1787_);
lean_inc(v___y_1788_);
v___f_1795_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1795_, 0, v_k_1784_);
lean_closure_set(v___f_1795_, 1, v___x_1794_);
lean_closure_set(v___f_1795_, 2, v___y_1788_);
v___x_1796_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1782_, v_maxFVars_x3f_1783_, v___f_1795_, v_cleanupAnnotations_1785_, v_whnfType_1786_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1796_) == 0)
{
return v___x_1796_;
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg___boxed(lean_object* v_type_1805_, lean_object* v_maxFVars_x3f_1806_, lean_object* v_k_1807_, lean_object* v_cleanupAnnotations_1808_, lean_object* v_whnfType_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1817_; uint8_t v_whnfType_boxed_1818_; uint8_t v___y_18309__boxed_1819_; lean_object* v_res_1820_; 
v_cleanupAnnotations_boxed_1817_ = lean_unbox(v_cleanupAnnotations_1808_);
v_whnfType_boxed_1818_ = lean_unbox(v_whnfType_1809_);
v___y_18309__boxed_1819_ = lean_unbox(v___y_1810_);
v_res_1820_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg(v_type_1805_, v_maxFVars_x3f_1806_, v_k_1807_, v_cleanupAnnotations_boxed_1817_, v_whnfType_boxed_1818_, v___y_18309__boxed_1819_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6(lean_object* v_00_u03b1_1821_, lean_object* v_type_1822_, lean_object* v_maxFVars_x3f_1823_, lean_object* v_k_1824_, uint8_t v_cleanupAnnotations_1825_, uint8_t v_whnfType_1826_, uint8_t v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg(v_type_1822_, v_maxFVars_x3f_1823_, v_k_1824_, v_cleanupAnnotations_1825_, v_whnfType_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___boxed(lean_object* v_00_u03b1_1835_, lean_object* v_type_1836_, lean_object* v_maxFVars_x3f_1837_, lean_object* v_k_1838_, lean_object* v_cleanupAnnotations_1839_, lean_object* v_whnfType_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1848_; uint8_t v_whnfType_boxed_1849_; uint8_t v___y_18353__boxed_1850_; lean_object* v_res_1851_; 
v_cleanupAnnotations_boxed_1848_ = lean_unbox(v_cleanupAnnotations_1839_);
v_whnfType_boxed_1849_ = lean_unbox(v_whnfType_1840_);
v___y_18353__boxed_1850_ = lean_unbox(v___y_1841_);
v_res_1851_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6(v_00_u03b1_1835_, v_type_1836_, v_maxFVars_x3f_1837_, v_k_1838_, v_cleanupAnnotations_boxed_1848_, v_whnfType_boxed_1849_, v___y_18353__boxed_1850_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object* v_m_1852_, lean_object* v_query_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v_zero_1857_; uint8_t v_isZero_1858_; 
v_zero_1857_ = lean_unsigned_to_nat(0u);
v_isZero_1858_ = lean_nat_dec_eq(v_x_1855_, v_zero_1857_);
if (v_isZero_1858_ == 1)
{
lean_dec(v_x_1856_);
lean_dec(v_x_1855_);
if (lean_obj_tag(v_x_1854_) == 0)
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_box(2);
return v___x_1859_;
}
else
{
lean_object* v_val_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v_val_1860_ = lean_ctor_get(v_x_1854_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_x_1854_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v_x_1854_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_val_1860_);
lean_dec(v_x_1854_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_val_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
else
{
lean_object* v_keyArray_1868_; lean_object* v_valueArray_1869_; lean_object* v___x_1870_; uint8_t v_isSome_1871_; 
v_keyArray_1868_ = lean_ctor_get(v_m_1852_, 1);
v_valueArray_1869_ = lean_ctor_get(v_m_1852_, 2);
v___x_1870_ = lean_array_fget_borrowed(v_keyArray_1868_, v_x_1856_);
v_isSome_1871_ = lean_noption_is_some(v___x_1870_);
if (v_isSome_1871_ == 0)
{
lean_dec(v_x_1855_);
if (lean_obj_tag(v_x_1854_) == 0)
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_x_1856_);
return v___x_1872_;
}
else
{
lean_object* v_val_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_x_1856_);
v_val_1873_ = lean_ctor_get(v_x_1854_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_x_1854_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v_x_1854_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_val_1873_);
lean_dec(v_x_1854_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_val_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v_one_1881_; lean_object* v_n_1882_; lean_object* v___y_1884_; 
v_one_1881_ = lean_unsigned_to_nat(1u);
v_n_1882_ = lean_nat_sub(v_x_1855_, v_one_1881_);
lean_dec(v_x_1855_);
if (v_isSome_1871_ == 0)
{
goto v___jp_1890_;
}
else
{
lean_object* v___x_1892_; uint8_t v_isSome_1893_; 
v___x_1892_ = lean_array_fget_borrowed(v_valueArray_1869_, v_x_1856_);
v_isSome_1893_ = lean_noption_is_some(v___x_1892_);
if (v_isSome_1893_ == 0)
{
goto v___jp_1890_;
}
else
{
lean_object* v_val_1894_; uint8_t v___x_1895_; 
lean_inc(v___x_1870_);
v_val_1894_ = lean_noption_get(v___x_1870_);
v___x_1895_ = l_Lean_ExprStructEq_beq(v_val_1894_, v_query_1853_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
lean_dec(v_val_1894_);
v___x_1896_ = lean_array_get_size(v_keyArray_1868_);
v___x_1897_ = lean_nat_add(v_x_1856_, v_one_1881_);
lean_dec(v_x_1856_);
v___x_1898_ = lean_nat_dec_lt(v___x_1897_, v___x_1896_);
if (v___x_1898_ == 0)
{
lean_dec(v___x_1897_);
v_x_1855_ = v_n_1882_;
v_x_1856_ = v_zero_1857_;
goto _start;
}
else
{
v_x_1855_ = v_n_1882_;
v_x_1856_ = v___x_1897_;
goto _start;
}
}
else
{
lean_object* v_val_1901_; lean_object* v___x_1902_; 
lean_dec(v_n_1882_);
lean_dec(v_x_1854_);
lean_inc(v___x_1892_);
v_val_1901_ = lean_noption_get(v___x_1892_);
v___x_1902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1902_, 0, v_x_1856_);
lean_ctor_set(v___x_1902_, 1, v_val_1894_);
lean_ctor_set(v___x_1902_, 2, v_val_1901_);
return v___x_1902_;
}
}
}
v___jp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1885_ = lean_array_get_size(v_keyArray_1868_);
v___x_1886_ = lean_nat_add(v_x_1856_, v_one_1881_);
lean_dec(v_x_1856_);
v___x_1887_ = lean_nat_dec_lt(v___x_1886_, v___x_1885_);
if (v___x_1887_ == 0)
{
lean_dec(v___x_1886_);
v_x_1854_ = v___y_1884_;
v_x_1855_ = v_n_1882_;
v_x_1856_ = v_zero_1857_;
goto _start;
}
else
{
v_x_1854_ = v___y_1884_;
v_x_1855_ = v_n_1882_;
v_x_1856_ = v___x_1886_;
goto _start;
}
}
v___jp_1890_:
{
if (lean_obj_tag(v_x_1854_) == 0)
{
lean_object* v___x_1891_; 
lean_inc(v_x_1856_);
v___x_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1891_, 0, v_x_1856_);
v___y_1884_ = v___x_1891_;
goto v___jp_1883_;
}
else
{
v___y_1884_ = v_x_1854_;
goto v___jp_1883_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object* v_m_1903_, lean_object* v_query_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_, lean_object* v_x_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_m_1903_, v_query_1904_, v_x_1905_, v_x_1906_, v_x_1907_);
lean_dec_ref(v_query_1904_);
lean_dec_ref(v_m_1903_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object* v_m_1909_, lean_object* v_query_1910_){
_start:
{
lean_object* v_keyArray_1911_; lean_object* v___x_1912_; uint64_t v___x_1913_; uint64_t v___x_1914_; uint64_t v___x_1915_; uint64_t v_fold_1916_; uint64_t v___x_1917_; uint64_t v___x_1918_; uint64_t v___x_1919_; size_t v___x_1920_; size_t v___x_1921_; size_t v___x_1922_; size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_keyArray_1911_ = lean_ctor_get(v_m_1909_, 1);
v___x_1912_ = lean_array_get_size(v_keyArray_1911_);
v___x_1913_ = l_Lean_ExprStructEq_hash(v_query_1910_);
v___x_1914_ = 32ULL;
v___x_1915_ = lean_uint64_shift_right(v___x_1913_, v___x_1914_);
v_fold_1916_ = lean_uint64_xor(v___x_1913_, v___x_1915_);
v___x_1917_ = 16ULL;
v___x_1918_ = lean_uint64_shift_right(v_fold_1916_, v___x_1917_);
v___x_1919_ = lean_uint64_xor(v_fold_1916_, v___x_1918_);
v___x_1920_ = lean_uint64_to_usize(v___x_1919_);
v___x_1921_ = lean_usize_of_nat(v___x_1912_);
v___x_1922_ = ((size_t)1ULL);
v___x_1923_ = lean_usize_sub(v___x_1921_, v___x_1922_);
v___x_1924_ = lean_usize_land(v___x_1920_, v___x_1923_);
v___x_1925_ = lean_usize_to_nat(v___x_1924_);
v___x_1926_ = lean_box(0);
v___x_1927_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_m_1909_, v_query_1910_, v___x_1926_, v___x_1912_, v___x_1925_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg___boxed(lean_object* v_m_1928_, lean_object* v_query_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_1928_, v_query_1929_);
lean_dec_ref(v_query_1929_);
lean_dec_ref(v_m_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object* v_m_1931_, lean_object* v_query_1932_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_1931_, v_query_1932_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_index_1934_; lean_object* v_key_1935_; lean_object* v_value_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v_index_1934_ = lean_ctor_get(v___x_1933_, 0);
v_key_1935_ = lean_ctor_get(v___x_1933_, 1);
v_value_1936_ = lean_ctor_get(v___x_1933_, 2);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1933_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_value_1936_);
lean_inc(v_key_1935_);
lean_inc(v_index_1934_);
lean_dec(v___x_1933_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_index_1934_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_key_1935_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v_value_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
else
{
lean_object* v___x_1944_; 
lean_dec(v___x_1933_);
v___x_1944_ = lean_box(1);
return v___x_1944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object* v_m_1945_, lean_object* v_query_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_m_1945_, v_query_1946_);
lean_dec_ref(v_query_1946_);
lean_dec_ref(v_m_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object* v_m_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_m_1948_, v_a_1949_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_value_1951_; lean_object* v___x_1952_; 
v_value_1951_ = lean_ctor_get(v___x_1950_, 2);
lean_inc(v_value_1951_);
lean_dec_ref_known(v___x_1950_, 3);
v___x_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1952_, 0, v_value_1951_);
return v___x_1952_;
}
else
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_box(0);
return v___x_1953_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object* v_m_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1954_, v_a_1955_);
lean_dec_ref(v_a_1955_);
lean_dec_ref(v_m_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4_spec__7___redArg(lean_object* v_b_1957_, lean_object* v_acc_1958_, lean_object* v_i_1959_){
_start:
{
lean_object* v___y_1961_; lean_object* v_keyArray_1969_; lean_object* v_valueArray_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_keyArray_1969_ = lean_ctor_get(v_b_1957_, 1);
v_valueArray_1970_ = lean_ctor_get(v_b_1957_, 2);
v___x_1971_ = lean_array_get_size(v_keyArray_1969_);
v___x_1972_ = lean_nat_dec_lt(v_i_1959_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_dec(v_i_1959_);
return v_acc_1958_;
}
else
{
lean_object* v___x_1973_; uint8_t v_isSome_1974_; 
v___x_1973_ = lean_array_fget_borrowed(v_keyArray_1969_, v_i_1959_);
v_isSome_1974_ = lean_noption_is_some(v___x_1973_);
if (v_isSome_1974_ == 0)
{
goto v___jp_1965_;
}
else
{
lean_object* v___x_1975_; uint8_t v_isSome_1976_; 
v___x_1975_ = lean_array_fget_borrowed(v_valueArray_1970_, v_i_1959_);
v_isSome_1976_ = lean_noption_is_some(v___x_1975_);
if (v_isSome_1976_ == 0)
{
goto v___jp_1965_;
}
else
{
lean_object* v_val_1977_; lean_object* v_val_1978_; lean_object* v_i_1980_; lean_object* v___x_1985_; 
lean_inc(v___x_1973_);
v_val_1977_ = lean_noption_get(v___x_1973_);
lean_inc(v___x_1975_);
v_val_1978_ = lean_noption_get(v___x_1975_);
v___x_1985_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_acc_1958_, v_val_1977_);
switch(lean_obj_tag(v___x_1985_))
{
case 0:
{
lean_object* v_index_1986_; lean_object* v_size_1987_; lean_object* v___x_1988_; 
v_index_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_index_1986_);
lean_dec_ref_known(v___x_1985_, 3);
v_size_1987_ = lean_ctor_get(v_acc_1958_, 0);
lean_inc(v_size_1987_);
v___x_1988_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1958_, v_size_1987_, v_index_1986_, v_val_1977_, v_val_1978_);
lean_dec(v_index_1986_);
v___y_1961_ = v___x_1988_;
goto v___jp_1960_;
}
case 1:
{
lean_object* v_index_1989_; 
v_index_1989_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_index_1989_);
lean_dec_ref_known(v___x_1985_, 1);
v_i_1980_ = v_index_1989_;
goto v___jp_1979_;
}
default: 
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1958_, v___x_1990_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_index_1992_; 
v_index_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_index_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v_i_1980_ = v_index_1992_;
goto v___jp_1979_;
}
else
{
lean_dec(v_val_1978_);
lean_dec(v_val_1977_);
v___y_1961_ = v_acc_1958_;
goto v___jp_1960_;
}
}
}
v___jp_1979_:
{
lean_object* v_size_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_size_1981_ = lean_ctor_get(v_acc_1958_, 0);
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = lean_nat_add(v_size_1981_, v___x_1982_);
v___x_1984_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1958_, v___x_1983_, v_i_1980_, v_val_1977_, v_val_1978_);
lean_dec(v_i_1980_);
v___y_1961_ = v___x_1984_;
goto v___jp_1960_;
}
}
}
}
v___jp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = lean_unsigned_to_nat(1u);
v___x_1963_ = lean_nat_add(v_i_1959_, v___x_1962_);
lean_dec(v_i_1959_);
v_acc_1958_ = v___y_1961_;
v_i_1959_ = v___x_1963_;
goto _start;
}
v___jp_1965_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = lean_unsigned_to_nat(1u);
v___x_1967_ = lean_nat_add(v_i_1959_, v___x_1966_);
lean_dec(v_i_1959_);
v_i_1959_ = v___x_1967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_b_1993_, lean_object* v_acc_1994_, lean_object* v_i_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4_spec__7___redArg(v_b_1993_, v_acc_1994_, v_i_1995_);
lean_dec_ref(v_b_1993_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4___redArg(lean_object* v_init_1997_, lean_object* v_b_1998_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_unsigned_to_nat(0u);
v___x_2000_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4_spec__7___redArg(v_b_1998_, v_init_1997_, v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4___redArg___boxed(lean_object* v_init_2001_, lean_object* v_b_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4___redArg(v_init_2001_, v_b_2002_);
lean_dec_ref(v_b_2002_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object* v_m_2004_){
_start:
{
lean_object* v_keyArray_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v_cellCount_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v_target_2012_; lean_object* v___x_2013_; 
v_keyArray_2005_ = lean_ctor_get(v_m_2004_, 1);
v___x_2006_ = lean_array_get_size(v_keyArray_2005_);
v___x_2007_ = lean_unsigned_to_nat(2u);
v_cellCount_2008_ = lean_nat_mul(v___x_2006_, v___x_2007_);
v___x_2009_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2008_);
v___x_2010_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2008_);
v___x_2011_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2008_);
v_target_2012_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2012_, 0, v___x_2009_);
lean_ctor_set(v_target_2012_, 1, v___x_2010_);
lean_ctor_set(v_target_2012_, 2, v___x_2011_);
v___x_2013_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4___redArg(v_target_2012_, v_m_2004_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object* v_m_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_m_2014_);
lean_dec_ref(v_m_2014_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__3___redArg(lean_object* v_x_2016_, lean_object* v_x_2017_, lean_object* v___y_2018_){
_start:
{
if (lean_obj_tag(v_x_2016_) == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = l_List_reverse___redArg(v_x_2017_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
else
{
lean_object* v_head_2022_; lean_object* v_tail_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2041_; 
v_head_2022_ = lean_ctor_get(v_x_2016_, 0);
v_tail_2023_ = lean_ctor_get(v_x_2016_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_x_2016_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2025_ = v_x_2016_;
v_isShared_2026_ = v_isSharedCheck_2041_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_tail_2023_);
lean_inc(v_head_2022_);
lean_dec(v_x_2016_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2041_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_Meta_Closure_collectLevel___redArg(v_head_2022_, v___y_2018_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 1, v_x_2017_);
lean_ctor_set(v___x_2025_, 0, v_a_2028_);
v___x_2030_ = v___x_2025_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2028_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_x_2017_);
v___x_2030_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
v_x_2016_ = v_tail_2023_;
v_x_2017_ = v___x_2030_;
goto _start;
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_del_object(v___x_2025_);
lean_dec(v_tail_2023_);
lean_dec(v_x_2017_);
v_a_2033_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2027_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2027_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__3___redArg___boxed(lean_object* v_x_2042_, lean_object* v_x_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__3___redArg(v_x_2042_, v_x_2043_, v___y_2044_);
lean_dec(v___y_2044_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object* v_e_2047_, lean_object* v_args_2048_, lean_object* v_x_2049_, uint8_t v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___x_2057_; uint8_t v___x_2058_; uint8_t v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; 
v___x_2057_ = l_Lean_mkAppN(v_e_2047_, v_args_2048_);
v___x_2058_ = 0;
v___x_2059_ = 1;
v___x_2060_ = 1;
v___x_2061_ = l_Lean_Meta_mkLambdaFVars(v_args_2048_, v___x_2057_, v___x_2058_, v___x_2059_, v___x_2058_, v___x_2059_, v___x_2060_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object* v_e_2062_, lean_object* v_args_2063_, lean_object* v_x_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
uint8_t v___y_18653__boxed_2072_; lean_object* v_res_2073_; 
v___y_18653__boxed_2072_ = lean_unbox(v___y_2065_);
v_res_2073_ = l_Lean_Meta_Closure_collectExprAux___lam__1(v_e_2062_, v_args_2063_, v_x_2064_, v___y_18653__boxed_2072_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v_x_2064_);
lean_dec_ref(v_args_2063_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4_spec__7___redArg(lean_object* v___y_2074_){
_start:
{
lean_object* v___x_2076_; lean_object* v_ngen_2077_; lean_object* v_namePrefix_2078_; lean_object* v_idx_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2108_; 
v___x_2076_ = lean_st_ref_get(v___y_2074_);
v_ngen_2077_ = lean_ctor_get(v___x_2076_, 2);
lean_inc_ref(v_ngen_2077_);
lean_dec(v___x_2076_);
v_namePrefix_2078_ = lean_ctor_get(v_ngen_2077_, 0);
v_idx_2079_ = lean_ctor_get(v_ngen_2077_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_ngen_2077_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2081_ = v_ngen_2077_;
v_isShared_2082_ = v_isSharedCheck_2108_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_idx_2079_);
lean_inc(v_namePrefix_2078_);
lean_dec(v_ngen_2077_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2108_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v_env_2084_; lean_object* v_nextMacroScope_2085_; lean_object* v_auxDeclNGen_2086_; lean_object* v_traceState_2087_; lean_object* v_cache_2088_; lean_object* v_messages_2089_; lean_object* v_infoState_2090_; lean_object* v_snapshotTasks_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2106_; 
v___x_2083_ = lean_st_ref_take(v___y_2074_);
v_env_2084_ = lean_ctor_get(v___x_2083_, 0);
v_nextMacroScope_2085_ = lean_ctor_get(v___x_2083_, 1);
v_auxDeclNGen_2086_ = lean_ctor_get(v___x_2083_, 3);
v_traceState_2087_ = lean_ctor_get(v___x_2083_, 4);
v_cache_2088_ = lean_ctor_get(v___x_2083_, 5);
v_messages_2089_ = lean_ctor_get(v___x_2083_, 6);
v_infoState_2090_ = lean_ctor_get(v___x_2083_, 7);
v_snapshotTasks_2091_ = lean_ctor_get(v___x_2083_, 8);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2106_ == 0)
{
lean_object* v_unused_2107_; 
v_unused_2107_ = lean_ctor_get(v___x_2083_, 2);
lean_dec(v_unused_2107_);
v___x_2093_ = v___x_2083_;
v_isShared_2094_ = v_isSharedCheck_2106_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_snapshotTasks_2091_);
lean_inc(v_infoState_2090_);
lean_inc(v_messages_2089_);
lean_inc(v_cache_2088_);
lean_inc(v_traceState_2087_);
lean_inc(v_auxDeclNGen_2086_);
lean_inc(v_nextMacroScope_2085_);
lean_inc(v_env_2084_);
lean_dec(v___x_2083_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2106_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_r_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
lean_inc(v_idx_2079_);
lean_inc(v_namePrefix_2078_);
v_r_2095_ = l_Lean_Name_num___override(v_namePrefix_2078_, v_idx_2079_);
v___x_2096_ = lean_unsigned_to_nat(1u);
v___x_2097_ = lean_nat_add(v_idx_2079_, v___x_2096_);
lean_dec(v_idx_2079_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v___x_2097_);
v___x_2099_ = v___x_2081_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_namePrefix_2078_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2101_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 2, v___x_2099_);
v___x_2101_ = v___x_2093_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_env_2084_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_nextMacroScope_2085_);
lean_ctor_set(v_reuseFailAlloc_2104_, 2, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2104_, 3, v_auxDeclNGen_2086_);
lean_ctor_set(v_reuseFailAlloc_2104_, 4, v_traceState_2087_);
lean_ctor_set(v_reuseFailAlloc_2104_, 5, v_cache_2088_);
lean_ctor_set(v_reuseFailAlloc_2104_, 6, v_messages_2089_);
lean_ctor_set(v_reuseFailAlloc_2104_, 7, v_infoState_2090_);
lean_ctor_set(v_reuseFailAlloc_2104_, 8, v_snapshotTasks_2091_);
v___x_2101_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_st_ref_put(v___y_2074_, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v_r_2095_);
return v___x_2103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4_spec__7___redArg___boxed(lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4_spec__7___redArg(v___y_2109_);
lean_dec(v___y_2109_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4(uint8_t v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v___x_2119_; lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
v___x_2119_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4_spec__7___redArg(v___y_2117_);
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
uint8_t v___y_18734__boxed_2135_; lean_object* v_res_2136_; 
v___y_18734__boxed_2135_ = lean_unbox(v___y_2128_);
v_res_2136_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4(v___y_18734__boxed_2135_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* v_e_2137_, uint8_t v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
switch(lean_obj_tag(v_e_2137_))
{
case 11:
{
lean_object* v_typeName_2145_; lean_object* v_idx_2146_; lean_object* v_struct_2147_; lean_object* v___x_2148_; 
v_typeName_2145_ = lean_ctor_get(v_e_2137_, 0);
v_idx_2146_ = lean_ctor_get(v_e_2137_, 1);
v_struct_2147_ = lean_ctor_get(v_e_2137_, 2);
lean_inc_ref(v_struct_2147_);
v___x_2148_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_struct_2147_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2163_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2151_ = v___x_2148_;
v_isShared_2152_ = v_isSharedCheck_2163_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2148_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2163_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
size_t v___x_2153_; size_t v___x_2154_; uint8_t v___x_2155_; 
v___x_2153_ = lean_ptr_addr(v_struct_2147_);
v___x_2154_ = lean_ptr_addr(v_a_2149_);
v___x_2155_ = lean_usize_dec_eq(v___x_2153_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
lean_inc(v_idx_2146_);
lean_inc(v_typeName_2145_);
lean_dec_ref_known(v_e_2137_, 3);
v___x_2156_ = l_Lean_Expr_proj___override(v_typeName_2145_, v_idx_2146_, v_a_2149_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2156_);
v___x_2158_ = v___x_2151_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
else
{
lean_object* v___x_2161_; 
lean_dec(v_a_2149_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v_e_2137_);
v___x_2161_ = v___x_2151_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_e_2137_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2137_, 3);
return v___x_2148_;
}
}
case 7:
{
lean_object* v_binderName_2164_; lean_object* v_binderType_2165_; lean_object* v_body_2166_; uint8_t v_binderInfo_2167_; lean_object* v___x_2168_; 
v_binderName_2164_ = lean_ctor_get(v_e_2137_, 0);
v_binderType_2165_ = lean_ctor_get(v_e_2137_, 1);
v_body_2166_ = lean_ctor_get(v_e_2137_, 2);
v_binderInfo_2167_ = lean_ctor_get_uint8(v_e_2137_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2165_);
v___x_2168_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_2165_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2170_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
lean_inc_ref(v_body_2166_);
v___x_2170_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_2166_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2195_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2195_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2195_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
uint8_t v___y_2176_; size_t v___x_2189_; size_t v___x_2190_; uint8_t v___x_2191_; 
v___x_2189_ = lean_ptr_addr(v_binderType_2165_);
v___x_2190_ = lean_ptr_addr(v_a_2169_);
v___x_2191_ = lean_usize_dec_eq(v___x_2189_, v___x_2190_);
if (v___x_2191_ == 0)
{
v___y_2176_ = v___x_2191_;
goto v___jp_2175_;
}
else
{
size_t v___x_2192_; size_t v___x_2193_; uint8_t v___x_2194_; 
v___x_2192_ = lean_ptr_addr(v_body_2166_);
v___x_2193_ = lean_ptr_addr(v_a_2171_);
v___x_2194_ = lean_usize_dec_eq(v___x_2192_, v___x_2193_);
v___y_2176_ = v___x_2194_;
goto v___jp_2175_;
}
v___jp_2175_:
{
if (v___y_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2179_; 
lean_inc(v_binderName_2164_);
lean_dec_ref_known(v_e_2137_, 3);
v___x_2177_ = l_Lean_Expr_forallE___override(v_binderName_2164_, v_a_2169_, v_a_2171_, v_binderInfo_2167_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2177_);
v___x_2179_ = v___x_2173_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
else
{
uint8_t v___x_2181_; 
v___x_2181_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2167_, v_binderInfo_2167_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
lean_inc(v_binderName_2164_);
lean_dec_ref_known(v_e_2137_, 3);
v___x_2182_ = l_Lean_Expr_forallE___override(v_binderName_2164_, v_a_2169_, v_a_2171_, v_binderInfo_2167_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2182_);
v___x_2184_ = v___x_2173_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
else
{
lean_object* v___x_2187_; 
lean_dec(v_a_2171_);
lean_dec(v_a_2169_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v_e_2137_);
v___x_2187_ = v___x_2173_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_e_2137_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2169_);
lean_dec_ref_known(v_e_2137_, 3);
return v___x_2170_;
}
}
else
{
lean_dec_ref_known(v_e_2137_, 3);
return v___x_2168_;
}
}
case 6:
{
lean_object* v_binderName_2196_; lean_object* v_binderType_2197_; lean_object* v_body_2198_; uint8_t v_binderInfo_2199_; lean_object* v___x_2200_; 
v_binderName_2196_ = lean_ctor_get(v_e_2137_, 0);
v_binderType_2197_ = lean_ctor_get(v_e_2137_, 1);
v_body_2198_ = lean_ctor_get(v_e_2137_, 2);
v_binderInfo_2199_ = lean_ctor_get_uint8(v_e_2137_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2197_);
v___x_2200_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_2197_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2200_, 1);
lean_inc_ref(v_body_2198_);
v___x_2202_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_2198_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2227_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2227_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2227_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
uint8_t v___y_2208_; size_t v___x_2221_; size_t v___x_2222_; uint8_t v___x_2223_; 
v___x_2221_ = lean_ptr_addr(v_binderType_2197_);
v___x_2222_ = lean_ptr_addr(v_a_2201_);
v___x_2223_ = lean_usize_dec_eq(v___x_2221_, v___x_2222_);
if (v___x_2223_ == 0)
{
v___y_2208_ = v___x_2223_;
goto v___jp_2207_;
}
else
{
size_t v___x_2224_; size_t v___x_2225_; uint8_t v___x_2226_; 
v___x_2224_ = lean_ptr_addr(v_body_2198_);
v___x_2225_ = lean_ptr_addr(v_a_2203_);
v___x_2226_ = lean_usize_dec_eq(v___x_2224_, v___x_2225_);
v___y_2208_ = v___x_2226_;
goto v___jp_2207_;
}
v___jp_2207_:
{
if (v___y_2208_ == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
lean_inc(v_binderName_2196_);
lean_dec_ref_known(v_e_2137_, 3);
v___x_2209_ = l_Lean_Expr_lam___override(v_binderName_2196_, v_a_2201_, v_a_2203_, v_binderInfo_2199_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2209_);
v___x_2211_ = v___x_2205_;
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
uint8_t v___x_2213_; 
v___x_2213_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2199_, v_binderInfo_2199_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
lean_inc(v_binderName_2196_);
lean_dec_ref_known(v_e_2137_, 3);
v___x_2214_ = l_Lean_Expr_lam___override(v_binderName_2196_, v_a_2201_, v_a_2203_, v_binderInfo_2199_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2214_);
v___x_2216_ = v___x_2205_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
else
{
lean_object* v___x_2219_; 
lean_dec(v_a_2203_);
lean_dec(v_a_2201_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v_e_2137_);
v___x_2219_ = v___x_2205_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_e_2137_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2201_);
lean_dec_ref_known(v_e_2137_, 3);
return v___x_2202_;
}
}
else
{
lean_dec_ref_known(v_e_2137_, 3);
return v___x_2200_;
}
}
case 8:
{
lean_object* v_declName_2228_; lean_object* v_type_2229_; lean_object* v_value_2230_; lean_object* v_body_2231_; uint8_t v_nondep_2232_; lean_object* v___x_2233_; 
v_declName_2228_ = lean_ctor_get(v_e_2137_, 0);
v_type_2229_ = lean_ctor_get(v_e_2137_, 1);
v_value_2230_ = lean_ctor_get(v_e_2137_, 2);
v_body_2231_ = lean_ctor_get(v_e_2137_, 3);
v_nondep_2232_ = lean_ctor_get_uint8(v_e_2137_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2229_);
v___x_2233_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_type_2229_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
lean_inc_ref(v_value_2230_);
v___x_2235_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_value_2230_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2237_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
lean_inc_ref(v_body_2231_);
v___x_2237_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_2231_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2264_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2264_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2264_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
uint8_t v___y_2243_; size_t v___x_2258_; size_t v___x_2259_; uint8_t v___x_2260_; 
v___x_2258_ = lean_ptr_addr(v_type_2229_);
v___x_2259_ = lean_ptr_addr(v_a_2234_);
v___x_2260_ = lean_usize_dec_eq(v___x_2258_, v___x_2259_);
if (v___x_2260_ == 0)
{
v___y_2243_ = v___x_2260_;
goto v___jp_2242_;
}
else
{
size_t v___x_2261_; size_t v___x_2262_; uint8_t v___x_2263_; 
v___x_2261_ = lean_ptr_addr(v_value_2230_);
v___x_2262_ = lean_ptr_addr(v_a_2236_);
v___x_2263_ = lean_usize_dec_eq(v___x_2261_, v___x_2262_);
v___y_2243_ = v___x_2263_;
goto v___jp_2242_;
}
v___jp_2242_:
{
if (v___y_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2246_; 
lean_inc(v_declName_2228_);
lean_dec_ref_known(v_e_2137_, 4);
v___x_2244_ = l_Lean_Expr_letE___override(v_declName_2228_, v_a_2234_, v_a_2236_, v_a_2238_, v_nondep_2232_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2244_);
v___x_2246_ = v___x_2240_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
else
{
size_t v___x_2248_; size_t v___x_2249_; uint8_t v___x_2250_; 
v___x_2248_ = lean_ptr_addr(v_body_2231_);
v___x_2249_ = lean_ptr_addr(v_a_2238_);
v___x_2250_ = lean_usize_dec_eq(v___x_2248_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2253_; 
lean_inc(v_declName_2228_);
lean_dec_ref_known(v_e_2137_, 4);
v___x_2251_ = l_Lean_Expr_letE___override(v_declName_2228_, v_a_2234_, v_a_2236_, v_a_2238_, v_nondep_2232_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2251_);
v___x_2253_ = v___x_2240_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
else
{
lean_object* v___x_2256_; 
lean_dec(v_a_2238_);
lean_dec(v_a_2236_);
lean_dec(v_a_2234_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v_e_2137_);
v___x_2256_ = v___x_2240_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_e_2137_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2236_);
lean_dec(v_a_2234_);
lean_dec_ref_known(v_e_2137_, 4);
return v___x_2237_;
}
}
else
{
lean_dec(v_a_2234_);
lean_dec_ref_known(v_e_2137_, 4);
return v___x_2235_;
}
}
else
{
lean_dec_ref_known(v_e_2137_, 4);
return v___x_2233_;
}
}
case 5:
{
lean_object* v_fn_2265_; lean_object* v_arg_2266_; lean_object* v___x_2267_; 
v_fn_2265_ = lean_ctor_get(v_e_2137_, 0);
v_arg_2266_ = lean_ctor_get(v_e_2137_, 1);
lean_inc_ref(v_fn_2265_);
v___x_2267_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_fn_2265_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2269_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
lean_inc_ref(v_arg_2266_);
v___x_2269_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_arg_2266_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2289_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2289_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2289_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
uint8_t v___y_2275_; size_t v___x_2283_; size_t v___x_2284_; uint8_t v___x_2285_; 
v___x_2283_ = lean_ptr_addr(v_fn_2265_);
v___x_2284_ = lean_ptr_addr(v_a_2268_);
v___x_2285_ = lean_usize_dec_eq(v___x_2283_, v___x_2284_);
if (v___x_2285_ == 0)
{
v___y_2275_ = v___x_2285_;
goto v___jp_2274_;
}
else
{
size_t v___x_2286_; size_t v___x_2287_; uint8_t v___x_2288_; 
v___x_2286_ = lean_ptr_addr(v_arg_2266_);
v___x_2287_ = lean_ptr_addr(v_a_2270_);
v___x_2288_ = lean_usize_dec_eq(v___x_2286_, v___x_2287_);
v___y_2275_ = v___x_2288_;
goto v___jp_2274_;
}
v___jp_2274_:
{
if (v___y_2275_ == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
lean_dec_ref_known(v_e_2137_, 2);
v___x_2276_ = l_Lean_Expr_app___override(v_a_2268_, v_a_2270_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2276_);
v___x_2278_ = v___x_2272_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
else
{
lean_object* v___x_2281_; 
lean_dec(v_a_2270_);
lean_dec(v_a_2268_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v_e_2137_);
v___x_2281_ = v___x_2272_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_e_2137_);
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
else
{
lean_dec(v_a_2268_);
lean_dec_ref_known(v_e_2137_, 2);
return v___x_2269_;
}
}
else
{
lean_dec_ref_known(v_e_2137_, 2);
return v___x_2267_;
}
}
case 10:
{
lean_object* v_data_2290_; lean_object* v_expr_2291_; lean_object* v___x_2292_; 
v_data_2290_ = lean_ctor_get(v_e_2137_, 0);
v_expr_2291_ = lean_ctor_get(v_e_2137_, 1);
lean_inc_ref(v_expr_2291_);
v___x_2292_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_expr_2291_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2307_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2307_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2307_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
size_t v___x_2297_; size_t v___x_2298_; uint8_t v___x_2299_; 
v___x_2297_ = lean_ptr_addr(v_expr_2291_);
v___x_2298_ = lean_ptr_addr(v_a_2293_);
v___x_2299_ = lean_usize_dec_eq(v___x_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
lean_inc(v_data_2290_);
lean_dec_ref_known(v_e_2137_, 2);
v___x_2300_ = l_Lean_Expr_mdata___override(v_data_2290_, v_a_2293_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2300_);
v___x_2302_ = v___x_2295_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
else
{
lean_object* v___x_2305_; 
lean_dec(v_a_2293_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v_e_2137_);
v___x_2305_ = v___x_2295_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_e_2137_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2137_, 2);
return v___x_2292_;
}
}
case 3:
{
lean_object* v_u_2308_; lean_object* v___x_2309_; 
v_u_2308_ = lean_ctor_get(v_e_2137_, 0);
lean_inc(v_u_2308_);
v___x_2309_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_2308_, v_a_2139_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2324_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2324_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2324_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
size_t v___x_2314_; size_t v___x_2315_; uint8_t v___x_2316_; 
v___x_2314_ = lean_ptr_addr(v_u_2308_);
v___x_2315_ = lean_ptr_addr(v_a_2310_);
v___x_2316_ = lean_usize_dec_eq(v___x_2314_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
lean_dec_ref_known(v_e_2137_, 1);
v___x_2317_ = l_Lean_Expr_sort___override(v_a_2310_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2317_);
v___x_2319_ = v___x_2312_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
else
{
lean_object* v___x_2322_; 
lean_dec(v_a_2310_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v_e_2137_);
v___x_2322_ = v___x_2312_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_e_2137_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec_ref_known(v_e_2137_, 1);
v_a_2325_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2309_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2309_);
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
case 4:
{
lean_object* v_declName_2333_; lean_object* v_us_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_declName_2333_ = lean_ctor_get(v_e_2137_, 0);
v_us_2334_ = lean_ctor_get(v_e_2137_, 1);
v___x_2335_ = lean_box(0);
lean_inc(v_us_2334_);
v___x_2336_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__3___redArg(v_us_2334_, v___x_2335_, v_a_2139_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2349_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2349_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2349_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
uint8_t v___x_2341_; 
v___x_2341_ = l_ptrEqList___redArg(v_us_2334_, v_a_2337_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
lean_inc(v_declName_2333_);
lean_dec_ref_known(v_e_2137_, 2);
v___x_2342_ = l_Lean_Expr_const___override(v_declName_2333_, v_a_2337_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2342_);
v___x_2344_ = v___x_2339_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
else
{
lean_object* v___x_2347_; 
lean_dec(v_a_2337_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v_e_2137_);
v___x_2347_ = v___x_2339_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_e_2137_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref_known(v_e_2137_, 2);
v_a_2350_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2336_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2336_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_2358_; lean_object* v___x_2359_; 
v_mvarId_2358_ = lean_ctor_get(v_e_2137_, 0);
lean_inc(v_mvarId_2358_);
v___x_2359_ = l_Lean_MVarId_getDecl(v_mvarId_2358_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v_type_2361_; lean_object* v___x_2362_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v_type_2361_ = lean_ctor_get(v_a_2360_, 2);
lean_inc_ref_n(v_type_2361_, 2);
lean_dec(v_a_2360_);
v___x_2362_ = l_Lean_Meta_Closure_preprocess(v_type_2361_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2364_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v___x_2364_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_2363_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2366_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4(v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_2139_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2431_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2431_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2431_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v_e_x27_2374_; lean_object* v___y_2375_; lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_mvarId_2358_, v_a_2141_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
if (lean_obj_tag(v_a_2408_) == 1)
{
lean_object* v_val_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2422_; 
v_val_2409_ = lean_ctor_get(v_a_2408_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_a_2408_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2411_ = v_a_2408_;
v_isShared_2412_ = v_isSharedCheck_2422_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_val_2409_);
lean_dec(v_a_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2422_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v_fvars_2413_; lean_object* v___f_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
v_fvars_2413_ = lean_ctor_get(v_val_2409_, 0);
lean_inc_ref(v_fvars_2413_);
lean_dec(v_val_2409_);
v___f_2414_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2414_, 0, v_e_2137_);
v___x_2415_ = lean_array_get_size(v_fvars_2413_);
lean_dec_ref(v_fvars_2413_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2415_);
v___x_2417_ = v___x_2411_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
uint8_t v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = 0;
v___x_2419_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__6___redArg(v_type_2361_, v___x_2417_, v___f_2414_, v___x_2418_, v___x_2418_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2419_, 1);
v_e_x27_2374_ = v_a_2420_;
v___y_2375_ = v_a_2139_;
goto v___jp_2373_;
}
else
{
lean_del_object(v___x_2371_);
lean_dec(v_a_2369_);
lean_dec(v_a_2367_);
lean_dec(v_a_2365_);
return v___x_2419_;
}
}
}
}
else
{
lean_dec(v_a_2408_);
lean_dec_ref(v_type_2361_);
v_e_x27_2374_ = v_e_2137_;
v___y_2375_ = v_a_2139_;
goto v___jp_2373_;
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_del_object(v___x_2371_);
lean_dec(v_a_2369_);
lean_dec(v_a_2367_);
lean_dec(v_a_2365_);
lean_dec_ref(v_type_2361_);
lean_dec_ref_known(v_e_2137_, 1);
v_a_2423_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2407_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2407_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
v___jp_2373_:
{
lean_object* v___x_2376_; lean_object* v_visitedLevel_2377_; lean_object* v_visitedExpr_2378_; lean_object* v_levelParams_2379_; lean_object* v_nextLevelIdx_2380_; lean_object* v_levelArgs_2381_; lean_object* v_newLocalDecls_2382_; lean_object* v_newLocalDeclsForMVars_2383_; lean_object* v_newLetDecls_2384_; lean_object* v_nextExprIdx_2385_; lean_object* v_exprMVarArgs_2386_; lean_object* v_exprFVarArgs_2387_; lean_object* v_toProcess_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2406_; 
v___x_2376_ = lean_st_ref_take(v___y_2375_);
v_visitedLevel_2377_ = lean_ctor_get(v___x_2376_, 0);
v_visitedExpr_2378_ = lean_ctor_get(v___x_2376_, 1);
v_levelParams_2379_ = lean_ctor_get(v___x_2376_, 2);
v_nextLevelIdx_2380_ = lean_ctor_get(v___x_2376_, 3);
v_levelArgs_2381_ = lean_ctor_get(v___x_2376_, 4);
v_newLocalDecls_2382_ = lean_ctor_get(v___x_2376_, 5);
v_newLocalDeclsForMVars_2383_ = lean_ctor_get(v___x_2376_, 6);
v_newLetDecls_2384_ = lean_ctor_get(v___x_2376_, 7);
v_nextExprIdx_2385_ = lean_ctor_get(v___x_2376_, 8);
v_exprMVarArgs_2386_ = lean_ctor_get(v___x_2376_, 9);
v_exprFVarArgs_2387_ = lean_ctor_get(v___x_2376_, 10);
v_toProcess_2388_ = lean_ctor_get(v___x_2376_, 11);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2390_ = v___x_2376_;
v_isShared_2391_ = v_isSharedCheck_2406_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_toProcess_2388_);
lean_inc(v_exprFVarArgs_2387_);
lean_inc(v_exprMVarArgs_2386_);
lean_inc(v_nextExprIdx_2385_);
lean_inc(v_newLetDecls_2384_);
lean_inc(v_newLocalDeclsForMVars_2383_);
lean_inc(v_newLocalDecls_2382_);
lean_inc(v_levelArgs_2381_);
lean_inc(v_nextLevelIdx_2380_);
lean_inc(v_levelParams_2379_);
lean_inc(v_visitedExpr_2378_);
lean_inc(v_visitedLevel_2377_);
lean_dec(v___x_2376_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2406_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; uint8_t v___x_2393_; uint8_t v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
v___x_2392_ = lean_unsigned_to_nat(0u);
v___x_2393_ = 0;
v___x_2394_ = 0;
lean_inc(v_a_2367_);
v___x_2395_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2395_, 0, v___x_2392_);
lean_ctor_set(v___x_2395_, 1, v_a_2367_);
lean_ctor_set(v___x_2395_, 2, v_a_2369_);
lean_ctor_set(v___x_2395_, 3, v_a_2365_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*4, v___x_2393_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*4 + 1, v___x_2394_);
v___x_2396_ = lean_array_push(v_newLocalDeclsForMVars_2383_, v___x_2395_);
v___x_2397_ = lean_array_push(v_exprMVarArgs_2386_, v_e_x27_2374_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 9, v___x_2397_);
lean_ctor_set(v___x_2390_, 6, v___x_2396_);
v___x_2399_ = v___x_2390_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_visitedLevel_2377_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_visitedExpr_2378_);
lean_ctor_set(v_reuseFailAlloc_2405_, 2, v_levelParams_2379_);
lean_ctor_set(v_reuseFailAlloc_2405_, 3, v_nextLevelIdx_2380_);
lean_ctor_set(v_reuseFailAlloc_2405_, 4, v_levelArgs_2381_);
lean_ctor_set(v_reuseFailAlloc_2405_, 5, v_newLocalDecls_2382_);
lean_ctor_set(v_reuseFailAlloc_2405_, 6, v___x_2396_);
lean_ctor_set(v_reuseFailAlloc_2405_, 7, v_newLetDecls_2384_);
lean_ctor_set(v_reuseFailAlloc_2405_, 8, v_nextExprIdx_2385_);
lean_ctor_set(v_reuseFailAlloc_2405_, 9, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2405_, 10, v_exprFVarArgs_2387_);
lean_ctor_set(v_reuseFailAlloc_2405_, 11, v_toProcess_2388_);
v___x_2399_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2400_ = lean_st_ref_put(v___y_2375_, v___x_2399_);
v___x_2401_ = l_Lean_mkFVar(v_a_2367_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2401_);
v___x_2403_ = v___x_2371_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec(v_a_2367_);
lean_dec(v_a_2365_);
lean_dec_ref(v_type_2361_);
lean_dec_ref_known(v_e_2137_, 1);
v_a_2432_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2368_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2368_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v_a_2365_);
lean_dec_ref(v_type_2361_);
lean_dec_ref_known(v_e_2137_, 1);
v_a_2440_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2366_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2366_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
else
{
lean_dec_ref(v_type_2361_);
lean_dec_ref_known(v_e_2137_, 1);
return v___x_2364_;
}
}
else
{
lean_dec_ref(v_type_2361_);
lean_dec_ref_known(v_e_2137_, 1);
return v___x_2362_;
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec_ref_known(v_e_2137_, 1);
v_a_2448_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2359_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2359_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_2456_; uint8_t v___x_2457_; lean_object* v___x_2458_; 
v_fvarId_2456_ = lean_ctor_get(v_e_2137_, 0);
lean_inc_n(v_fvarId_2456_, 2);
lean_dec_ref_known(v_e_2137_, 1);
v___x_2457_ = 0;
v___x_2458_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_2456_, v___x_2457_, v_a_2140_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; uint8_t v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
if (v_a_2138_ == 1)
{
if (lean_obj_tag(v_a_2459_) == 1)
{
lean_object* v_val_2496_; lean_object* v___x_2497_; 
lean_dec(v_fvarId_2456_);
v_val_2496_ = lean_ctor_get(v_a_2459_, 0);
lean_inc(v_val_2496_);
lean_dec_ref_known(v_a_2459_, 1);
v___x_2497_ = l_Lean_Meta_Closure_preprocess(v_val_2496_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2499_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_2498_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
return v___x_2499_;
}
else
{
return v___x_2497_;
}
}
else
{
lean_dec(v_a_2459_);
v___y_2461_ = v_a_2138_;
v___y_2462_ = v_a_2139_;
v___y_2463_ = v_a_2140_;
v___y_2464_ = v_a_2141_;
v___y_2465_ = v_a_2142_;
v___y_2466_ = v_a_2143_;
goto v___jp_2460_;
}
}
else
{
lean_dec(v_a_2459_);
v___y_2461_ = v_a_2138_;
v___y_2462_ = v_a_2139_;
v___y_2463_ = v_a_2140_;
v___y_2464_ = v_a_2141_;
v___y_2465_ = v_a_2142_;
v___y_2466_ = v_a_2143_;
goto v___jp_2460_;
}
v___jp_2460_:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4(v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc_n(v_a_2468_, 2);
lean_dec_ref_known(v___x_2467_, 1);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v_fvarId_2456_);
lean_ctor_set(v___x_2469_, 1, v_a_2468_);
v___x_2470_ = l_Lean_Meta_Closure_pushToProcess___redArg(v___x_2469_, v___y_2462_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2478_; 
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v___x_2470_, 0);
lean_dec(v_unused_2479_);
v___x_2472_ = v___x_2470_;
v_isShared_2473_ = v_isSharedCheck_2478_;
goto v_resetjp_2471_;
}
else
{
lean_dec(v___x_2470_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2478_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2474_ = l_Lean_mkFVar(v_a_2468_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2474_);
v___x_2476_ = v___x_2472_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec(v_a_2468_);
v_a_2480_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2470_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2470_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v_fvarId_2456_);
v_a_2488_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2467_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2467_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_fvarId_2456_);
v_a_2500_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2458_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2458_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
default: 
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_e_2137_);
return v___x_2508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object* v_e_2509_, uint8_t v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v_i_2548_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v_i_2590_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; uint8_t v___x_2674_; 
v___x_2674_ = l_Lean_Expr_hasLevelParam(v_e_2509_);
if (v___x_2674_ == 0)
{
uint8_t v___x_2675_; 
v___x_2675_ = l_Lean_Expr_hasFVar(v_e_2509_);
if (v___x_2675_ == 0)
{
uint8_t v___x_2676_; 
v___x_2676_ = l_Lean_Expr_hasMVar(v_e_2509_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2677_, 0, v_e_2509_);
return v___x_2677_;
}
else
{
goto v___jp_2617_;
}
}
else
{
goto v___jp_2617_;
}
}
else
{
goto v___jp_2617_;
}
v___jp_2517_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2531_, 0, v___y_2519_);
lean_ctor_set(v___x_2531_, 1, v___y_2530_);
lean_ctor_set(v___x_2531_, 2, v___y_2525_);
lean_ctor_set(v___x_2531_, 3, v___y_2529_);
lean_ctor_set(v___x_2531_, 4, v___y_2518_);
lean_ctor_set(v___x_2531_, 5, v___y_2524_);
lean_ctor_set(v___x_2531_, 6, v___y_2528_);
lean_ctor_set(v___x_2531_, 7, v___y_2527_);
lean_ctor_set(v___x_2531_, 8, v___y_2522_);
lean_ctor_set(v___x_2531_, 9, v___y_2521_);
lean_ctor_set(v___x_2531_, 10, v___y_2520_);
lean_ctor_set(v___x_2531_, 11, v___y_2526_);
v___x_2532_ = lean_st_ref_put(v___y_2511_, v___x_2531_);
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___y_2523_);
return v___x_2533_;
}
v___jp_2534_:
{
lean_object* v_size_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v_size_2549_ = lean_ctor_get(v___y_2547_, 0);
v___x_2550_ = lean_unsigned_to_nat(1u);
v___x_2551_ = lean_nat_add(v_size_2549_, v___x_2550_);
lean_inc_ref(v___y_2540_);
v___x_2552_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2547_, v___x_2551_, v_i_2548_, v_e_2509_, v___y_2540_);
lean_dec(v_i_2548_);
v___y_2518_ = v___y_2535_;
v___y_2519_ = v___y_2536_;
v___y_2520_ = v___y_2537_;
v___y_2521_ = v___y_2538_;
v___y_2522_ = v___y_2539_;
v___y_2523_ = v___y_2540_;
v___y_2524_ = v___y_2541_;
v___y_2525_ = v___y_2542_;
v___y_2526_ = v___y_2543_;
v___y_2527_ = v___y_2544_;
v___y_2528_ = v___y_2545_;
v___y_2529_ = v___y_2546_;
v___y_2530_ = v___x_2552_;
goto v___jp_2517_;
}
v___jp_2553_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v___y_2558_);
lean_dec_ref(v___y_2558_);
v___x_2568_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v___x_2567_, v_e_2509_);
switch(lean_obj_tag(v___x_2568_))
{
case 0:
{
lean_object* v_index_2569_; lean_object* v_size_2570_; lean_object* v___x_2571_; 
v_index_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_index_2569_);
lean_dec_ref_known(v___x_2568_, 3);
v_size_2570_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_size_2570_);
lean_inc_ref(v___y_2560_);
v___x_2571_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2567_, v_size_2570_, v_index_2569_, v_e_2509_, v___y_2560_);
lean_dec(v_index_2569_);
v___y_2518_ = v___y_2554_;
v___y_2519_ = v___y_2555_;
v___y_2520_ = v___y_2556_;
v___y_2521_ = v___y_2557_;
v___y_2522_ = v___y_2559_;
v___y_2523_ = v___y_2560_;
v___y_2524_ = v___y_2561_;
v___y_2525_ = v___y_2562_;
v___y_2526_ = v___y_2563_;
v___y_2527_ = v___y_2564_;
v___y_2528_ = v___y_2565_;
v___y_2529_ = v___y_2566_;
v___y_2530_ = v___x_2571_;
goto v___jp_2517_;
}
case 1:
{
lean_object* v_index_2572_; 
v_index_2572_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_index_2572_);
lean_dec_ref_known(v___x_2568_, 1);
v___y_2535_ = v___y_2554_;
v___y_2536_ = v___y_2555_;
v___y_2537_ = v___y_2556_;
v___y_2538_ = v___y_2557_;
v___y_2539_ = v___y_2559_;
v___y_2540_ = v___y_2560_;
v___y_2541_ = v___y_2561_;
v___y_2542_ = v___y_2562_;
v___y_2543_ = v___y_2563_;
v___y_2544_ = v___y_2564_;
v___y_2545_ = v___y_2565_;
v___y_2546_ = v___y_2566_;
v___y_2547_ = v___x_2567_;
v_i_2548_ = v_index_2572_;
goto v___jp_2534_;
}
default: 
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2567_, v___x_2573_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_index_2575_; 
v_index_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_index_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___y_2535_ = v___y_2554_;
v___y_2536_ = v___y_2555_;
v___y_2537_ = v___y_2556_;
v___y_2538_ = v___y_2557_;
v___y_2539_ = v___y_2559_;
v___y_2540_ = v___y_2560_;
v___y_2541_ = v___y_2561_;
v___y_2542_ = v___y_2562_;
v___y_2543_ = v___y_2563_;
v___y_2544_ = v___y_2564_;
v___y_2545_ = v___y_2565_;
v___y_2546_ = v___y_2566_;
v___y_2547_ = v___x_2567_;
v_i_2548_ = v_index_2575_;
goto v___jp_2534_;
}
else
{
lean_dec_ref(v_e_2509_);
v___y_2518_ = v___y_2554_;
v___y_2519_ = v___y_2555_;
v___y_2520_ = v___y_2556_;
v___y_2521_ = v___y_2557_;
v___y_2522_ = v___y_2559_;
v___y_2523_ = v___y_2560_;
v___y_2524_ = v___y_2561_;
v___y_2525_ = v___y_2562_;
v___y_2526_ = v___y_2563_;
v___y_2527_ = v___y_2564_;
v___y_2528_ = v___y_2565_;
v___y_2529_ = v___y_2566_;
v___y_2530_ = v___x_2567_;
goto v___jp_2517_;
}
}
}
}
v___jp_2576_:
{
lean_object* v_size_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_size_2591_ = lean_ctor_get(v___y_2581_, 0);
v___x_2592_ = lean_unsigned_to_nat(1u);
v___x_2593_ = lean_nat_add(v_size_2591_, v___x_2592_);
lean_inc_ref(v___y_2583_);
v___x_2594_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2581_, v___x_2593_, v_i_2590_, v_e_2509_, v___y_2583_);
lean_dec(v_i_2590_);
v___y_2518_ = v___y_2577_;
v___y_2519_ = v___y_2578_;
v___y_2520_ = v___y_2579_;
v___y_2521_ = v___y_2580_;
v___y_2522_ = v___y_2582_;
v___y_2523_ = v___y_2583_;
v___y_2524_ = v___y_2584_;
v___y_2525_ = v___y_2585_;
v___y_2526_ = v___y_2586_;
v___y_2527_ = v___y_2587_;
v___y_2528_ = v___y_2588_;
v___y_2529_ = v___y_2589_;
v___y_2530_ = v___x_2594_;
goto v___jp_2517_;
}
v___jp_2595_:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v___y_2608_, v_e_2509_);
switch(lean_obj_tag(v___x_2609_))
{
case 0:
{
lean_object* v_index_2610_; lean_object* v_size_2611_; lean_object* v___x_2612_; 
v_index_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_index_2610_);
lean_dec_ref_known(v___x_2609_, 3);
v_size_2611_ = lean_ctor_get(v___y_2608_, 0);
lean_inc(v_size_2611_);
lean_inc_ref(v___y_2601_);
v___x_2612_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2608_, v_size_2611_, v_index_2610_, v_e_2509_, v___y_2601_);
lean_dec(v_index_2610_);
v___y_2518_ = v___y_2596_;
v___y_2519_ = v___y_2597_;
v___y_2520_ = v___y_2598_;
v___y_2521_ = v___y_2599_;
v___y_2522_ = v___y_2600_;
v___y_2523_ = v___y_2601_;
v___y_2524_ = v___y_2602_;
v___y_2525_ = v___y_2603_;
v___y_2526_ = v___y_2604_;
v___y_2527_ = v___y_2605_;
v___y_2528_ = v___y_2606_;
v___y_2529_ = v___y_2607_;
v___y_2530_ = v___x_2612_;
goto v___jp_2517_;
}
case 1:
{
lean_object* v_index_2613_; 
v_index_2613_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_index_2613_);
lean_dec_ref_known(v___x_2609_, 1);
v___y_2577_ = v___y_2596_;
v___y_2578_ = v___y_2597_;
v___y_2579_ = v___y_2598_;
v___y_2580_ = v___y_2599_;
v___y_2581_ = v___y_2608_;
v___y_2582_ = v___y_2600_;
v___y_2583_ = v___y_2601_;
v___y_2584_ = v___y_2602_;
v___y_2585_ = v___y_2603_;
v___y_2586_ = v___y_2604_;
v___y_2587_ = v___y_2605_;
v___y_2588_ = v___y_2606_;
v___y_2589_ = v___y_2607_;
v_i_2590_ = v_index_2613_;
goto v___jp_2576_;
}
default: 
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = lean_unsigned_to_nat(0u);
v___x_2615_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2608_, v___x_2614_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_index_2616_; 
v_index_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_index_2616_);
lean_dec_ref_known(v___x_2615_, 1);
v___y_2577_ = v___y_2596_;
v___y_2578_ = v___y_2597_;
v___y_2579_ = v___y_2598_;
v___y_2580_ = v___y_2599_;
v___y_2581_ = v___y_2608_;
v___y_2582_ = v___y_2600_;
v___y_2583_ = v___y_2601_;
v___y_2584_ = v___y_2602_;
v___y_2585_ = v___y_2603_;
v___y_2586_ = v___y_2604_;
v___y_2587_ = v___y_2605_;
v___y_2588_ = v___y_2606_;
v___y_2589_ = v___y_2607_;
v_i_2590_ = v_index_2616_;
goto v___jp_2576_;
}
else
{
lean_dec_ref(v_e_2509_);
v___y_2518_ = v___y_2596_;
v___y_2519_ = v___y_2597_;
v___y_2520_ = v___y_2598_;
v___y_2521_ = v___y_2599_;
v___y_2522_ = v___y_2600_;
v___y_2523_ = v___y_2601_;
v___y_2524_ = v___y_2602_;
v___y_2525_ = v___y_2603_;
v___y_2526_ = v___y_2604_;
v___y_2527_ = v___y_2605_;
v___y_2528_ = v___y_2606_;
v___y_2529_ = v___y_2607_;
v___y_2530_ = v___y_2608_;
goto v___jp_2517_;
}
}
}
}
v___jp_2617_:
{
lean_object* v___x_2618_; lean_object* v_visitedExpr_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_st_ref_get(v___y_2511_);
v_visitedExpr_2619_ = lean_ctor_get(v___x_2618_, 1);
lean_inc_ref(v_visitedExpr_2619_);
lean_dec(v___x_2618_);
v___x_2620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_2619_, v_e_2509_);
lean_dec_ref(v_visitedExpr_2619_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v___x_2621_; 
lean_inc_ref(v_e_2509_);
v___x_2621_ = l_Lean_Meta_Closure_collectExprAux(v_e_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2623_; lean_object* v_visitedLevel_2624_; lean_object* v_visitedExpr_2625_; lean_object* v_levelParams_2626_; lean_object* v_nextLevelIdx_2627_; lean_object* v_levelArgs_2628_; lean_object* v_newLocalDecls_2629_; lean_object* v_newLocalDeclsForMVars_2630_; lean_object* v_newLetDecls_2631_; lean_object* v_nextExprIdx_2632_; lean_object* v_exprMVarArgs_2633_; lean_object* v_exprFVarArgs_2634_; lean_object* v_toProcess_2635_; lean_object* v___x_2636_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2623_ = lean_st_ref_take(v___y_2511_);
v_visitedLevel_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc_ref(v_visitedLevel_2624_);
v_visitedExpr_2625_ = lean_ctor_get(v___x_2623_, 1);
lean_inc_ref(v_visitedExpr_2625_);
v_levelParams_2626_ = lean_ctor_get(v___x_2623_, 2);
lean_inc_ref(v_levelParams_2626_);
v_nextLevelIdx_2627_ = lean_ctor_get(v___x_2623_, 3);
lean_inc(v_nextLevelIdx_2627_);
v_levelArgs_2628_ = lean_ctor_get(v___x_2623_, 4);
lean_inc_ref(v_levelArgs_2628_);
v_newLocalDecls_2629_ = lean_ctor_get(v___x_2623_, 5);
lean_inc_ref(v_newLocalDecls_2629_);
v_newLocalDeclsForMVars_2630_ = lean_ctor_get(v___x_2623_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_2630_);
v_newLetDecls_2631_ = lean_ctor_get(v___x_2623_, 7);
lean_inc_ref(v_newLetDecls_2631_);
v_nextExprIdx_2632_ = lean_ctor_get(v___x_2623_, 8);
lean_inc(v_nextExprIdx_2632_);
v_exprMVarArgs_2633_ = lean_ctor_get(v___x_2623_, 9);
lean_inc_ref(v_exprMVarArgs_2633_);
v_exprFVarArgs_2634_ = lean_ctor_get(v___x_2623_, 10);
lean_inc_ref(v_exprFVarArgs_2634_);
v_toProcess_2635_ = lean_ctor_get(v___x_2623_, 11);
lean_inc_ref(v_toProcess_2635_);
lean_dec(v___x_2623_);
v___x_2636_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_2625_, v_e_2509_);
switch(lean_obj_tag(v___x_2636_))
{
case 0:
{
lean_object* v_index_2637_; lean_object* v_size_2638_; lean_object* v___x_2639_; 
v_index_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_index_2637_);
lean_dec_ref_known(v___x_2636_, 3);
v_size_2638_ = lean_ctor_get(v_visitedExpr_2625_, 0);
lean_inc(v_size_2638_);
lean_inc(v_a_2622_);
v___x_2639_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedExpr_2625_, v_size_2638_, v_index_2637_, v_e_2509_, v_a_2622_);
lean_dec(v_index_2637_);
v___y_2518_ = v_levelArgs_2628_;
v___y_2519_ = v_visitedLevel_2624_;
v___y_2520_ = v_exprFVarArgs_2634_;
v___y_2521_ = v_exprMVarArgs_2633_;
v___y_2522_ = v_nextExprIdx_2632_;
v___y_2523_ = v_a_2622_;
v___y_2524_ = v_newLocalDecls_2629_;
v___y_2525_ = v_levelParams_2626_;
v___y_2526_ = v_toProcess_2635_;
v___y_2527_ = v_newLetDecls_2631_;
v___y_2528_ = v_newLocalDeclsForMVars_2630_;
v___y_2529_ = v_nextLevelIdx_2627_;
v___y_2530_ = v___x_2639_;
goto v___jp_2517_;
}
case 1:
{
lean_object* v_index_2640_; lean_object* v_size_2641_; lean_object* v_keyArray_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v_index_2640_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_index_2640_);
lean_dec_ref_known(v___x_2636_, 1);
v_size_2641_ = lean_ctor_get(v_visitedExpr_2625_, 0);
v_keyArray_2642_ = lean_ctor_get(v_visitedExpr_2625_, 1);
v___x_2643_ = lean_unsigned_to_nat(1u);
v___x_2644_ = lean_nat_add(v_size_2641_, v___x_2643_);
v___x_2645_ = lean_array_get_size(v_keyArray_2642_);
v___x_2646_ = lean_nat_dec_lt(v___x_2644_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_dec(v___x_2644_);
lean_dec(v_index_2640_);
v___y_2554_ = v_levelArgs_2628_;
v___y_2555_ = v_visitedLevel_2624_;
v___y_2556_ = v_exprFVarArgs_2634_;
v___y_2557_ = v_exprMVarArgs_2633_;
v___y_2558_ = v_visitedExpr_2625_;
v___y_2559_ = v_nextExprIdx_2632_;
v___y_2560_ = v_a_2622_;
v___y_2561_ = v_newLocalDecls_2629_;
v___y_2562_ = v_levelParams_2626_;
v___y_2563_ = v_toProcess_2635_;
v___y_2564_ = v_newLetDecls_2631_;
v___y_2565_ = v_newLocalDeclsForMVars_2630_;
v___y_2566_ = v_nextLevelIdx_2627_;
goto v___jp_2553_;
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2647_ = lean_unsigned_to_nat(4u);
v___x_2648_ = lean_nat_mul(v___x_2644_, v___x_2647_);
v___x_2649_ = lean_unsigned_to_nat(3u);
v___x_2650_ = lean_nat_mul(v___x_2645_, v___x_2649_);
v___x_2651_ = lean_nat_dec_le(v___x_2648_, v___x_2650_);
lean_dec(v___x_2650_);
lean_dec(v___x_2648_);
if (v___x_2651_ == 0)
{
lean_dec(v___x_2644_);
lean_dec(v_index_2640_);
v___y_2554_ = v_levelArgs_2628_;
v___y_2555_ = v_visitedLevel_2624_;
v___y_2556_ = v_exprFVarArgs_2634_;
v___y_2557_ = v_exprMVarArgs_2633_;
v___y_2558_ = v_visitedExpr_2625_;
v___y_2559_ = v_nextExprIdx_2632_;
v___y_2560_ = v_a_2622_;
v___y_2561_ = v_newLocalDecls_2629_;
v___y_2562_ = v_levelParams_2626_;
v___y_2563_ = v_toProcess_2635_;
v___y_2564_ = v_newLetDecls_2631_;
v___y_2565_ = v_newLocalDeclsForMVars_2630_;
v___y_2566_ = v_nextLevelIdx_2627_;
goto v___jp_2553_;
}
else
{
lean_object* v___x_2652_; 
lean_inc(v_a_2622_);
v___x_2652_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedExpr_2625_, v___x_2644_, v_index_2640_, v_e_2509_, v_a_2622_);
lean_dec(v_index_2640_);
v___y_2518_ = v_levelArgs_2628_;
v___y_2519_ = v_visitedLevel_2624_;
v___y_2520_ = v_exprFVarArgs_2634_;
v___y_2521_ = v_exprMVarArgs_2633_;
v___y_2522_ = v_nextExprIdx_2632_;
v___y_2523_ = v_a_2622_;
v___y_2524_ = v_newLocalDecls_2629_;
v___y_2525_ = v_levelParams_2626_;
v___y_2526_ = v_toProcess_2635_;
v___y_2527_ = v_newLetDecls_2631_;
v___y_2528_ = v_newLocalDeclsForMVars_2630_;
v___y_2529_ = v_nextLevelIdx_2627_;
v___y_2530_ = v___x_2652_;
goto v___jp_2517_;
}
}
}
default: 
{
lean_object* v_size_2653_; lean_object* v_keyArray_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v_size_2653_ = lean_ctor_get(v_visitedExpr_2625_, 0);
v_keyArray_2654_ = lean_ctor_get(v_visitedExpr_2625_, 1);
v___x_2655_ = lean_unsigned_to_nat(1u);
v___x_2656_ = lean_nat_add(v_size_2653_, v___x_2655_);
v___x_2657_ = lean_array_get_size(v_keyArray_2654_);
v___x_2658_ = lean_nat_dec_lt(v___x_2656_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; 
lean_dec(v___x_2656_);
v___x_2659_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_visitedExpr_2625_);
lean_dec_ref(v_visitedExpr_2625_);
v___y_2596_ = v_levelArgs_2628_;
v___y_2597_ = v_visitedLevel_2624_;
v___y_2598_ = v_exprFVarArgs_2634_;
v___y_2599_ = v_exprMVarArgs_2633_;
v___y_2600_ = v_nextExprIdx_2632_;
v___y_2601_ = v_a_2622_;
v___y_2602_ = v_newLocalDecls_2629_;
v___y_2603_ = v_levelParams_2626_;
v___y_2604_ = v_toProcess_2635_;
v___y_2605_ = v_newLetDecls_2631_;
v___y_2606_ = v_newLocalDeclsForMVars_2630_;
v___y_2607_ = v_nextLevelIdx_2627_;
v___y_2608_ = v___x_2659_;
goto v___jp_2595_;
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2660_ = lean_unsigned_to_nat(4u);
v___x_2661_ = lean_nat_mul(v___x_2656_, v___x_2660_);
lean_dec(v___x_2656_);
v___x_2662_ = lean_unsigned_to_nat(3u);
v___x_2663_ = lean_nat_mul(v___x_2657_, v___x_2662_);
v___x_2664_ = lean_nat_dec_le(v___x_2661_, v___x_2663_);
lean_dec(v___x_2663_);
lean_dec(v___x_2661_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_visitedExpr_2625_);
lean_dec_ref(v_visitedExpr_2625_);
v___y_2596_ = v_levelArgs_2628_;
v___y_2597_ = v_visitedLevel_2624_;
v___y_2598_ = v_exprFVarArgs_2634_;
v___y_2599_ = v_exprMVarArgs_2633_;
v___y_2600_ = v_nextExprIdx_2632_;
v___y_2601_ = v_a_2622_;
v___y_2602_ = v_newLocalDecls_2629_;
v___y_2603_ = v_levelParams_2626_;
v___y_2604_ = v_toProcess_2635_;
v___y_2605_ = v_newLetDecls_2631_;
v___y_2606_ = v_newLocalDeclsForMVars_2630_;
v___y_2607_ = v_nextLevelIdx_2627_;
v___y_2608_ = v___x_2665_;
goto v___jp_2595_;
}
else
{
v___y_2596_ = v_levelArgs_2628_;
v___y_2597_ = v_visitedLevel_2624_;
v___y_2598_ = v_exprFVarArgs_2634_;
v___y_2599_ = v_exprMVarArgs_2633_;
v___y_2600_ = v_nextExprIdx_2632_;
v___y_2601_ = v_a_2622_;
v___y_2602_ = v_newLocalDecls_2629_;
v___y_2603_ = v_levelParams_2626_;
v___y_2604_ = v_toProcess_2635_;
v___y_2605_ = v_newLetDecls_2631_;
v___y_2606_ = v_newLocalDeclsForMVars_2630_;
v___y_2607_ = v_nextLevelIdx_2627_;
v___y_2608_ = v_visitedExpr_2625_;
goto v___jp_2595_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2509_);
return v___x_2621_;
}
}
else
{
lean_object* v_val_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec_ref(v_e_2509_);
v_val_2666_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2620_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_val_2666_);
lean_dec(v___x_2620_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set_tag(v___x_2668_, 0);
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_val_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object* v_e_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
uint8_t v___y_18774__boxed_2686_; lean_object* v_res_2687_; 
v___y_18774__boxed_2686_ = lean_unbox(v___y_2679_);
v_res_2687_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_e_2678_, v___y_18774__boxed_2686_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* v_e_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
uint8_t v_a_boxed_2696_; lean_object* v_res_2697_; 
v_a_boxed_2696_ = lean_unbox(v_a_2689_);
v_res_2697_ = l_Lean_Meta_Closure_collectExprAux(v_e_2688_, v_a_boxed_2696_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object* v_00_u03b2_2698_, lean_object* v_m_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_2699_, v_a_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object* v_00_u03b2_2702_, lean_object* v_m_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(v_00_u03b2_2702_, v_m_2703_, v_a_2704_);
lean_dec_ref(v_a_2704_);
lean_dec_ref(v_m_2703_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object* v_00_u03b2_2706_, lean_object* v_m_2707_, lean_object* v_query_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_2707_, v_query_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___boxed(lean_object* v_00_u03b2_2710_, lean_object* v_m_2711_, lean_object* v_query_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1(v_00_u03b2_2710_, v_m_2711_, v_query_2712_);
lean_dec_ref(v_query_2712_);
lean_dec_ref(v_m_2711_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object* v_00_u03b2_2714_, lean_object* v_m_2715_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_m_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object* v_00_u03b2_2717_, lean_object* v_m_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2(v_00_u03b2_2717_, v_m_2718_);
lean_dec_ref(v_m_2718_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__3(lean_object* v_x_2720_, lean_object* v_x_2721_, uint8_t v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__3___redArg(v_x_2720_, v_x_2721_, v___y_2723_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object* v_x_2730_, lean_object* v_x_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
uint8_t v___y_19798__boxed_2739_; lean_object* v_res_2740_; 
v___y_19798__boxed_2739_ = lean_unbox(v___y_2732_);
v_res_2740_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__3(v_x_2730_, v_x_2731_, v___y_19798__boxed_2739_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4_spec__7(uint8_t v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4_spec__7___redArg(v___y_2746_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4_spec__7___boxed(lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
uint8_t v___y_19825__boxed_2756_; lean_object* v_res_2757_; 
v___y_19825__boxed_2756_ = lean_unbox(v___y_2749_);
v_res_2757_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__4_spec__7(v___y_19825__boxed_2756_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object* v_00_u03b2_2758_, lean_object* v_m_2759_, lean_object* v_query_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_m_2759_, v_query_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2762_, lean_object* v_m_2763_, lean_object* v_query_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(v_00_u03b2_2762_, v_m_2763_, v_query_2764_);
lean_dec_ref(v_query_2764_);
lean_dec_ref(v_m_2763_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object* v_00_u03b2_2766_, lean_object* v_m_2767_, lean_object* v_query_2768_, lean_object* v_x_2769_, lean_object* v_x_2770_, lean_object* v_x_2771_, lean_object* v_x_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_m_2767_, v_query_2768_, v_x_2769_, v_x_2770_, v_x_2771_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2774_, lean_object* v_m_2775_, lean_object* v_query_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_, lean_object* v_x_2779_, lean_object* v_x_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(v_00_u03b2_2774_, v_m_2775_, v_query_2776_, v_x_2777_, v_x_2778_, v_x_2779_, v_x_2780_);
lean_dec_ref(v_query_2776_);
lean_dec_ref(v_m_2775_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4(lean_object* v_00_u03b2_2782_, lean_object* v_init_2783_, lean_object* v_b_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4___redArg(v_init_2783_, v_b_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2786_, lean_object* v_init_2787_, lean_object* v_b_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4(v_00_u03b2_2786_, v_init_2787_, v_b_2788_);
lean_dec_ref(v_b_2788_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_2790_, lean_object* v_b_2791_, lean_object* v_acc_2792_, lean_object* v_i_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4_spec__7___redArg(v_b_2791_, v_acc_2792_, v_i_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_2795_, lean_object* v_b_2796_, lean_object* v_acc_2797_, lean_object* v_i_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2_spec__4_spec__7(v_00_u03b2_2795_, v_b_2796_, v_acc_2797_, v_i_2798_);
lean_dec_ref(v_b_2796_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* v_e_2800_, uint8_t v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_Meta_Closure_preprocess(v_e_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v_i_2841_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v_i_2882_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; uint8_t v___x_2967_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
v___x_2967_ = l_Lean_Expr_hasLevelParam(v_a_2826_);
if (v___x_2967_ == 0)
{
uint8_t v___x_2968_; 
v___x_2968_ = l_Lean_Expr_hasFVar(v_a_2826_);
if (v___x_2968_ == 0)
{
uint8_t v___x_2969_; 
v___x_2969_ = l_Lean_Expr_hasMVar(v_a_2826_);
if (v___x_2969_ == 0)
{
lean_dec(v_a_2826_);
return v___x_2825_;
}
else
{
lean_dec_ref_known(v___x_2825_, 1);
goto v___jp_2910_;
}
}
else
{
lean_dec_ref_known(v___x_2825_, 1);
goto v___jp_2910_;
}
}
else
{
lean_dec_ref_known(v___x_2825_, 1);
goto v___jp_2910_;
}
v___jp_2827_:
{
lean_object* v_size_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v_size_2842_ = lean_ctor_get(v___y_2836_, 0);
v___x_2843_ = lean_unsigned_to_nat(1u);
v___x_2844_ = lean_nat_add(v_size_2842_, v___x_2843_);
lean_inc_ref(v___y_2829_);
v___x_2845_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2836_, v___x_2844_, v_i_2841_, v_a_2826_, v___y_2829_);
lean_dec(v_i_2841_);
v___y_2809_ = v___y_2828_;
v___y_2810_ = v___y_2829_;
v___y_2811_ = v___y_2830_;
v___y_2812_ = v___y_2831_;
v___y_2813_ = v___y_2832_;
v___y_2814_ = v___y_2833_;
v___y_2815_ = v___y_2834_;
v___y_2816_ = v___y_2835_;
v___y_2817_ = v___y_2837_;
v___y_2818_ = v___y_2838_;
v___y_2819_ = v___y_2839_;
v___y_2820_ = v___y_2840_;
v___y_2821_ = v___x_2845_;
goto v___jp_2808_;
}
v___jp_2846_:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v___y_2859_, v_a_2826_);
switch(lean_obj_tag(v___x_2860_))
{
case 0:
{
lean_object* v_index_2861_; lean_object* v_size_2862_; lean_object* v___x_2863_; 
v_index_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_index_2861_);
lean_dec_ref_known(v___x_2860_, 3);
v_size_2862_ = lean_ctor_get(v___y_2859_, 0);
lean_inc(v_size_2862_);
lean_inc_ref(v___y_2848_);
v___x_2863_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2859_, v_size_2862_, v_index_2861_, v_a_2826_, v___y_2848_);
lean_dec(v_index_2861_);
v___y_2809_ = v___y_2847_;
v___y_2810_ = v___y_2848_;
v___y_2811_ = v___y_2849_;
v___y_2812_ = v___y_2850_;
v___y_2813_ = v___y_2851_;
v___y_2814_ = v___y_2852_;
v___y_2815_ = v___y_2853_;
v___y_2816_ = v___y_2854_;
v___y_2817_ = v___y_2855_;
v___y_2818_ = v___y_2856_;
v___y_2819_ = v___y_2857_;
v___y_2820_ = v___y_2858_;
v___y_2821_ = v___x_2863_;
goto v___jp_2808_;
}
case 1:
{
lean_object* v_index_2864_; 
v_index_2864_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_index_2864_);
lean_dec_ref_known(v___x_2860_, 1);
v___y_2828_ = v___y_2847_;
v___y_2829_ = v___y_2848_;
v___y_2830_ = v___y_2849_;
v___y_2831_ = v___y_2850_;
v___y_2832_ = v___y_2851_;
v___y_2833_ = v___y_2852_;
v___y_2834_ = v___y_2853_;
v___y_2835_ = v___y_2854_;
v___y_2836_ = v___y_2859_;
v___y_2837_ = v___y_2855_;
v___y_2838_ = v___y_2856_;
v___y_2839_ = v___y_2857_;
v___y_2840_ = v___y_2858_;
v_i_2841_ = v_index_2864_;
goto v___jp_2827_;
}
default: 
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = lean_unsigned_to_nat(0u);
v___x_2866_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2859_, v___x_2865_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_index_2867_; 
v_index_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_index_2867_);
lean_dec_ref_known(v___x_2866_, 1);
v___y_2828_ = v___y_2847_;
v___y_2829_ = v___y_2848_;
v___y_2830_ = v___y_2849_;
v___y_2831_ = v___y_2850_;
v___y_2832_ = v___y_2851_;
v___y_2833_ = v___y_2852_;
v___y_2834_ = v___y_2853_;
v___y_2835_ = v___y_2854_;
v___y_2836_ = v___y_2859_;
v___y_2837_ = v___y_2855_;
v___y_2838_ = v___y_2856_;
v___y_2839_ = v___y_2857_;
v___y_2840_ = v___y_2858_;
v_i_2841_ = v_index_2867_;
goto v___jp_2827_;
}
else
{
lean_dec(v_a_2826_);
v___y_2809_ = v___y_2847_;
v___y_2810_ = v___y_2848_;
v___y_2811_ = v___y_2849_;
v___y_2812_ = v___y_2850_;
v___y_2813_ = v___y_2851_;
v___y_2814_ = v___y_2852_;
v___y_2815_ = v___y_2853_;
v___y_2816_ = v___y_2854_;
v___y_2817_ = v___y_2855_;
v___y_2818_ = v___y_2856_;
v___y_2819_ = v___y_2857_;
v___y_2820_ = v___y_2858_;
v___y_2821_ = v___y_2859_;
goto v___jp_2808_;
}
}
}
}
v___jp_2868_:
{
lean_object* v_size_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_size_2883_ = lean_ctor_get(v___y_2875_, 0);
v___x_2884_ = lean_unsigned_to_nat(1u);
v___x_2885_ = lean_nat_add(v_size_2883_, v___x_2884_);
lean_inc_ref(v___y_2870_);
v___x_2886_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2875_, v___x_2885_, v_i_2882_, v_a_2826_, v___y_2870_);
lean_dec(v_i_2882_);
v___y_2809_ = v___y_2869_;
v___y_2810_ = v___y_2870_;
v___y_2811_ = v___y_2871_;
v___y_2812_ = v___y_2872_;
v___y_2813_ = v___y_2873_;
v___y_2814_ = v___y_2874_;
v___y_2815_ = v___y_2876_;
v___y_2816_ = v___y_2877_;
v___y_2817_ = v___y_2878_;
v___y_2818_ = v___y_2879_;
v___y_2819_ = v___y_2880_;
v___y_2820_ = v___y_2881_;
v___y_2821_ = v___x_2886_;
goto v___jp_2808_;
}
v___jp_2887_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v___y_2889_);
lean_dec_ref(v___y_2889_);
v___x_2902_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v___x_2901_, v_a_2826_);
switch(lean_obj_tag(v___x_2902_))
{
case 0:
{
lean_object* v_index_2903_; lean_object* v_size_2904_; lean_object* v___x_2905_; 
v_index_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_index_2903_);
lean_dec_ref_known(v___x_2902_, 3);
v_size_2904_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_size_2904_);
lean_inc_ref(v___y_2890_);
v___x_2905_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2901_, v_size_2904_, v_index_2903_, v_a_2826_, v___y_2890_);
lean_dec(v_index_2903_);
v___y_2809_ = v___y_2888_;
v___y_2810_ = v___y_2890_;
v___y_2811_ = v___y_2891_;
v___y_2812_ = v___y_2892_;
v___y_2813_ = v___y_2893_;
v___y_2814_ = v___y_2894_;
v___y_2815_ = v___y_2895_;
v___y_2816_ = v___y_2896_;
v___y_2817_ = v___y_2897_;
v___y_2818_ = v___y_2898_;
v___y_2819_ = v___y_2899_;
v___y_2820_ = v___y_2900_;
v___y_2821_ = v___x_2905_;
goto v___jp_2808_;
}
case 1:
{
lean_object* v_index_2906_; 
v_index_2906_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_index_2906_);
lean_dec_ref_known(v___x_2902_, 1);
v___y_2869_ = v___y_2888_;
v___y_2870_ = v___y_2890_;
v___y_2871_ = v___y_2891_;
v___y_2872_ = v___y_2892_;
v___y_2873_ = v___y_2893_;
v___y_2874_ = v___y_2894_;
v___y_2875_ = v___x_2901_;
v___y_2876_ = v___y_2895_;
v___y_2877_ = v___y_2896_;
v___y_2878_ = v___y_2897_;
v___y_2879_ = v___y_2898_;
v___y_2880_ = v___y_2899_;
v___y_2881_ = v___y_2900_;
v_i_2882_ = v_index_2906_;
goto v___jp_2868_;
}
default: 
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = lean_unsigned_to_nat(0u);
v___x_2908_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2901_, v___x_2907_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_index_2909_; 
v_index_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_index_2909_);
lean_dec_ref_known(v___x_2908_, 1);
v___y_2869_ = v___y_2888_;
v___y_2870_ = v___y_2890_;
v___y_2871_ = v___y_2891_;
v___y_2872_ = v___y_2892_;
v___y_2873_ = v___y_2893_;
v___y_2874_ = v___y_2894_;
v___y_2875_ = v___x_2901_;
v___y_2876_ = v___y_2895_;
v___y_2877_ = v___y_2896_;
v___y_2878_ = v___y_2897_;
v___y_2879_ = v___y_2898_;
v___y_2880_ = v___y_2899_;
v___y_2881_ = v___y_2900_;
v_i_2882_ = v_index_2909_;
goto v___jp_2868_;
}
else
{
lean_dec(v_a_2826_);
v___y_2809_ = v___y_2888_;
v___y_2810_ = v___y_2890_;
v___y_2811_ = v___y_2891_;
v___y_2812_ = v___y_2892_;
v___y_2813_ = v___y_2893_;
v___y_2814_ = v___y_2894_;
v___y_2815_ = v___y_2895_;
v___y_2816_ = v___y_2896_;
v___y_2817_ = v___y_2897_;
v___y_2818_ = v___y_2898_;
v___y_2819_ = v___y_2899_;
v___y_2820_ = v___y_2900_;
v___y_2821_ = v___x_2901_;
goto v___jp_2808_;
}
}
}
}
v___jp_2910_:
{
lean_object* v___x_2911_; lean_object* v_visitedExpr_2912_; lean_object* v___x_2913_; 
v___x_2911_ = lean_st_ref_get(v_a_2802_);
v_visitedExpr_2912_ = lean_ctor_get(v___x_2911_, 1);
lean_inc_ref(v_visitedExpr_2912_);
lean_dec(v___x_2911_);
v___x_2913_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_2912_, v_a_2826_);
lean_dec_ref(v_visitedExpr_2912_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v___x_2914_; 
lean_inc(v_a_2826_);
v___x_2914_ = l_Lean_Meta_Closure_collectExprAux(v_a_2826_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; lean_object* v_visitedLevel_2917_; lean_object* v_visitedExpr_2918_; lean_object* v_levelParams_2919_; lean_object* v_nextLevelIdx_2920_; lean_object* v_levelArgs_2921_; lean_object* v_newLocalDecls_2922_; lean_object* v_newLocalDeclsForMVars_2923_; lean_object* v_newLetDecls_2924_; lean_object* v_nextExprIdx_2925_; lean_object* v_exprMVarArgs_2926_; lean_object* v_exprFVarArgs_2927_; lean_object* v_toProcess_2928_; lean_object* v___x_2929_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
v___x_2916_ = lean_st_ref_take(v_a_2802_);
v_visitedLevel_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc_ref(v_visitedLevel_2917_);
v_visitedExpr_2918_ = lean_ctor_get(v___x_2916_, 1);
lean_inc_ref(v_visitedExpr_2918_);
v_levelParams_2919_ = lean_ctor_get(v___x_2916_, 2);
lean_inc_ref(v_levelParams_2919_);
v_nextLevelIdx_2920_ = lean_ctor_get(v___x_2916_, 3);
lean_inc(v_nextLevelIdx_2920_);
v_levelArgs_2921_ = lean_ctor_get(v___x_2916_, 4);
lean_inc_ref(v_levelArgs_2921_);
v_newLocalDecls_2922_ = lean_ctor_get(v___x_2916_, 5);
lean_inc_ref(v_newLocalDecls_2922_);
v_newLocalDeclsForMVars_2923_ = lean_ctor_get(v___x_2916_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_2923_);
v_newLetDecls_2924_ = lean_ctor_get(v___x_2916_, 7);
lean_inc_ref(v_newLetDecls_2924_);
v_nextExprIdx_2925_ = lean_ctor_get(v___x_2916_, 8);
lean_inc(v_nextExprIdx_2925_);
v_exprMVarArgs_2926_ = lean_ctor_get(v___x_2916_, 9);
lean_inc_ref(v_exprMVarArgs_2926_);
v_exprFVarArgs_2927_ = lean_ctor_get(v___x_2916_, 10);
lean_inc_ref(v_exprFVarArgs_2927_);
v_toProcess_2928_ = lean_ctor_get(v___x_2916_, 11);
lean_inc_ref(v_toProcess_2928_);
lean_dec(v___x_2916_);
v___x_2929_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_2918_, v_a_2826_);
switch(lean_obj_tag(v___x_2929_))
{
case 0:
{
lean_object* v_index_2930_; lean_object* v_size_2931_; lean_object* v___x_2932_; 
v_index_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_index_2930_);
lean_dec_ref_known(v___x_2929_, 3);
v_size_2931_ = lean_ctor_get(v_visitedExpr_2918_, 0);
lean_inc(v_size_2931_);
lean_inc(v_a_2915_);
v___x_2932_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedExpr_2918_, v_size_2931_, v_index_2930_, v_a_2826_, v_a_2915_);
lean_dec(v_index_2930_);
v___y_2809_ = v_nextLevelIdx_2920_;
v___y_2810_ = v_a_2915_;
v___y_2811_ = v_visitedLevel_2917_;
v___y_2812_ = v_exprFVarArgs_2927_;
v___y_2813_ = v_toProcess_2928_;
v___y_2814_ = v_newLocalDeclsForMVars_2923_;
v___y_2815_ = v_newLetDecls_2924_;
v___y_2816_ = v_levelArgs_2921_;
v___y_2817_ = v_levelParams_2919_;
v___y_2818_ = v_newLocalDecls_2922_;
v___y_2819_ = v_nextExprIdx_2925_;
v___y_2820_ = v_exprMVarArgs_2926_;
v___y_2821_ = v___x_2932_;
goto v___jp_2808_;
}
case 1:
{
lean_object* v_index_2933_; lean_object* v_size_2934_; lean_object* v_keyArray_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
v_index_2933_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_index_2933_);
lean_dec_ref_known(v___x_2929_, 1);
v_size_2934_ = lean_ctor_get(v_visitedExpr_2918_, 0);
v_keyArray_2935_ = lean_ctor_get(v_visitedExpr_2918_, 1);
v___x_2936_ = lean_unsigned_to_nat(1u);
v___x_2937_ = lean_nat_add(v_size_2934_, v___x_2936_);
v___x_2938_ = lean_array_get_size(v_keyArray_2935_);
v___x_2939_ = lean_nat_dec_lt(v___x_2937_, v___x_2938_);
if (v___x_2939_ == 0)
{
lean_dec(v___x_2937_);
lean_dec(v_index_2933_);
v___y_2888_ = v_nextLevelIdx_2920_;
v___y_2889_ = v_visitedExpr_2918_;
v___y_2890_ = v_a_2915_;
v___y_2891_ = v_visitedLevel_2917_;
v___y_2892_ = v_exprFVarArgs_2927_;
v___y_2893_ = v_toProcess_2928_;
v___y_2894_ = v_newLocalDeclsForMVars_2923_;
v___y_2895_ = v_newLetDecls_2924_;
v___y_2896_ = v_levelArgs_2921_;
v___y_2897_ = v_levelParams_2919_;
v___y_2898_ = v_newLocalDecls_2922_;
v___y_2899_ = v_nextExprIdx_2925_;
v___y_2900_ = v_exprMVarArgs_2926_;
goto v___jp_2887_;
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2940_ = lean_unsigned_to_nat(4u);
v___x_2941_ = lean_nat_mul(v___x_2937_, v___x_2940_);
v___x_2942_ = lean_unsigned_to_nat(3u);
v___x_2943_ = lean_nat_mul(v___x_2938_, v___x_2942_);
v___x_2944_ = lean_nat_dec_le(v___x_2941_, v___x_2943_);
lean_dec(v___x_2943_);
lean_dec(v___x_2941_);
if (v___x_2944_ == 0)
{
lean_dec(v___x_2937_);
lean_dec(v_index_2933_);
v___y_2888_ = v_nextLevelIdx_2920_;
v___y_2889_ = v_visitedExpr_2918_;
v___y_2890_ = v_a_2915_;
v___y_2891_ = v_visitedLevel_2917_;
v___y_2892_ = v_exprFVarArgs_2927_;
v___y_2893_ = v_toProcess_2928_;
v___y_2894_ = v_newLocalDeclsForMVars_2923_;
v___y_2895_ = v_newLetDecls_2924_;
v___y_2896_ = v_levelArgs_2921_;
v___y_2897_ = v_levelParams_2919_;
v___y_2898_ = v_newLocalDecls_2922_;
v___y_2899_ = v_nextExprIdx_2925_;
v___y_2900_ = v_exprMVarArgs_2926_;
goto v___jp_2887_;
}
else
{
lean_object* v___x_2945_; 
lean_inc(v_a_2915_);
v___x_2945_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedExpr_2918_, v___x_2937_, v_index_2933_, v_a_2826_, v_a_2915_);
lean_dec(v_index_2933_);
v___y_2809_ = v_nextLevelIdx_2920_;
v___y_2810_ = v_a_2915_;
v___y_2811_ = v_visitedLevel_2917_;
v___y_2812_ = v_exprFVarArgs_2927_;
v___y_2813_ = v_toProcess_2928_;
v___y_2814_ = v_newLocalDeclsForMVars_2923_;
v___y_2815_ = v_newLetDecls_2924_;
v___y_2816_ = v_levelArgs_2921_;
v___y_2817_ = v_levelParams_2919_;
v___y_2818_ = v_newLocalDecls_2922_;
v___y_2819_ = v_nextExprIdx_2925_;
v___y_2820_ = v_exprMVarArgs_2926_;
v___y_2821_ = v___x_2945_;
goto v___jp_2808_;
}
}
}
default: 
{
lean_object* v_size_2946_; lean_object* v_keyArray_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v_size_2946_ = lean_ctor_get(v_visitedExpr_2918_, 0);
v_keyArray_2947_ = lean_ctor_get(v_visitedExpr_2918_, 1);
v___x_2948_ = lean_unsigned_to_nat(1u);
v___x_2949_ = lean_nat_add(v_size_2946_, v___x_2948_);
v___x_2950_ = lean_array_get_size(v_keyArray_2947_);
v___x_2951_ = lean_nat_dec_lt(v___x_2949_, v___x_2950_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; 
lean_dec(v___x_2949_);
v___x_2952_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_visitedExpr_2918_);
lean_dec_ref(v_visitedExpr_2918_);
v___y_2847_ = v_nextLevelIdx_2920_;
v___y_2848_ = v_a_2915_;
v___y_2849_ = v_visitedLevel_2917_;
v___y_2850_ = v_exprFVarArgs_2927_;
v___y_2851_ = v_toProcess_2928_;
v___y_2852_ = v_newLocalDeclsForMVars_2923_;
v___y_2853_ = v_newLetDecls_2924_;
v___y_2854_ = v_levelArgs_2921_;
v___y_2855_ = v_levelParams_2919_;
v___y_2856_ = v_newLocalDecls_2922_;
v___y_2857_ = v_nextExprIdx_2925_;
v___y_2858_ = v_exprMVarArgs_2926_;
v___y_2859_ = v___x_2952_;
goto v___jp_2846_;
}
else
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2953_ = lean_unsigned_to_nat(4u);
v___x_2954_ = lean_nat_mul(v___x_2949_, v___x_2953_);
lean_dec(v___x_2949_);
v___x_2955_ = lean_unsigned_to_nat(3u);
v___x_2956_ = lean_nat_mul(v___x_2950_, v___x_2955_);
v___x_2957_ = lean_nat_dec_le(v___x_2954_, v___x_2956_);
lean_dec(v___x_2956_);
lean_dec(v___x_2954_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_visitedExpr_2918_);
lean_dec_ref(v_visitedExpr_2918_);
v___y_2847_ = v_nextLevelIdx_2920_;
v___y_2848_ = v_a_2915_;
v___y_2849_ = v_visitedLevel_2917_;
v___y_2850_ = v_exprFVarArgs_2927_;
v___y_2851_ = v_toProcess_2928_;
v___y_2852_ = v_newLocalDeclsForMVars_2923_;
v___y_2853_ = v_newLetDecls_2924_;
v___y_2854_ = v_levelArgs_2921_;
v___y_2855_ = v_levelParams_2919_;
v___y_2856_ = v_newLocalDecls_2922_;
v___y_2857_ = v_nextExprIdx_2925_;
v___y_2858_ = v_exprMVarArgs_2926_;
v___y_2859_ = v___x_2958_;
goto v___jp_2846_;
}
else
{
v___y_2847_ = v_nextLevelIdx_2920_;
v___y_2848_ = v_a_2915_;
v___y_2849_ = v_visitedLevel_2917_;
v___y_2850_ = v_exprFVarArgs_2927_;
v___y_2851_ = v_toProcess_2928_;
v___y_2852_ = v_newLocalDeclsForMVars_2923_;
v___y_2853_ = v_newLetDecls_2924_;
v___y_2854_ = v_levelArgs_2921_;
v___y_2855_ = v_levelParams_2919_;
v___y_2856_ = v_newLocalDecls_2922_;
v___y_2857_ = v_nextExprIdx_2925_;
v___y_2858_ = v_exprMVarArgs_2926_;
v___y_2859_ = v_visitedExpr_2918_;
goto v___jp_2846_;
}
}
}
}
}
else
{
lean_dec(v_a_2826_);
return v___x_2914_;
}
}
else
{
lean_object* v_val_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec(v_a_2826_);
v_val_2959_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2913_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_val_2959_);
lean_dec(v___x_2913_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set_tag(v___x_2961_, 0);
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_val_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
else
{
return v___x_2825_;
}
v___jp_2808_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2822_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2822_, 0, v___y_2811_);
lean_ctor_set(v___x_2822_, 1, v___y_2821_);
lean_ctor_set(v___x_2822_, 2, v___y_2817_);
lean_ctor_set(v___x_2822_, 3, v___y_2809_);
lean_ctor_set(v___x_2822_, 4, v___y_2816_);
lean_ctor_set(v___x_2822_, 5, v___y_2818_);
lean_ctor_set(v___x_2822_, 6, v___y_2814_);
lean_ctor_set(v___x_2822_, 7, v___y_2815_);
lean_ctor_set(v___x_2822_, 8, v___y_2819_);
lean_ctor_set(v___x_2822_, 9, v___y_2820_);
lean_ctor_set(v___x_2822_, 10, v___y_2812_);
lean_ctor_set(v___x_2822_, 11, v___y_2813_);
v___x_2823_ = lean_st_ref_put(v_a_2802_, v___x_2822_);
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___y_2810_);
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* v_e_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
uint8_t v_a_boxed_2978_; lean_object* v_res_2979_; 
v_a_boxed_2978_ = lean_unbox(v_a_2971_);
v_res_2979_ = l_Lean_Meta_Closure_collectExpr(v_e_2970_, v_a_boxed_2978_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_a_2974_);
lean_dec_ref(v_a_2973_);
lean_dec(v_a_2972_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* v_lctx_2980_, lean_object* v_i_2981_, lean_object* v_toProcess_2982_, lean_object* v_elem_2983_){
_start:
{
lean_object* v___x_2984_; uint8_t v___x_2985_; 
v___x_2984_ = lean_array_get_size(v_toProcess_2982_);
v___x_2985_ = lean_nat_dec_lt(v_i_2981_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
lean_dec(v_i_2981_);
lean_dec_ref(v_lctx_2980_);
v___x_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2986_, 0, v_elem_2983_);
lean_ctor_set(v___x_2986_, 1, v_toProcess_2982_);
return v___x_2986_;
}
else
{
lean_object* v_fvarId_2987_; lean_object* v_elem_x27_2988_; lean_object* v_fvarId_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v_fvarId_2987_ = lean_ctor_get(v_elem_2983_, 0);
v_elem_x27_2988_ = lean_array_fget_borrowed(v_toProcess_2982_, v_i_2981_);
v_fvarId_2989_ = lean_ctor_get(v_elem_x27_2988_, 0);
lean_inc(v_fvarId_2987_);
lean_inc_ref_n(v_lctx_2980_, 2);
v___x_2990_ = l_Lean_LocalContext_get_x21(v_lctx_2980_, v_fvarId_2987_);
v___x_2991_ = l_Lean_LocalDecl_index(v___x_2990_);
lean_dec_ref(v___x_2990_);
lean_inc(v_fvarId_2989_);
v___x_2992_ = l_Lean_LocalContext_get_x21(v_lctx_2980_, v_fvarId_2989_);
v___x_2993_ = l_Lean_LocalDecl_index(v___x_2992_);
lean_dec_ref(v___x_2992_);
v___x_2994_ = lean_nat_dec_lt(v___x_2991_, v___x_2993_);
lean_dec(v___x_2993_);
lean_dec(v___x_2991_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = lean_unsigned_to_nat(1u);
v___x_2996_ = lean_nat_add(v_i_2981_, v___x_2995_);
lean_dec(v_i_2981_);
v_i_2981_ = v___x_2996_;
goto _start;
}
else
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_inc(v_elem_x27_2988_);
v___x_2998_ = lean_unsigned_to_nat(1u);
v___x_2999_ = lean_nat_add(v_i_2981_, v___x_2998_);
v___x_3000_ = lean_array_fset(v_toProcess_2982_, v_i_2981_, v_elem_2983_);
lean_dec(v_i_2981_);
v_i_2981_ = v___x_2999_;
v_toProcess_2982_ = v___x_3000_;
v_elem_2983_ = v_elem_x27_2988_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v___x_3005_; lean_object* v_toProcess_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3005_ = lean_st_ref_get(v_a_3002_);
v_toProcess_3006_ = lean_ctor_get(v___x_3005_, 11);
lean_inc_ref(v_toProcess_3006_);
lean_dec(v___x_3005_);
v___x_3007_ = lean_array_get_size(v_toProcess_3006_);
lean_dec_ref(v_toProcess_3006_);
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = lean_nat_dec_eq(v___x_3007_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v_lctx_3011_; lean_object* v_visitedLevel_3012_; lean_object* v_visitedExpr_3013_; lean_object* v_levelParams_3014_; lean_object* v_nextLevelIdx_3015_; lean_object* v_levelArgs_3016_; lean_object* v_newLocalDecls_3017_; lean_object* v_newLocalDeclsForMVars_3018_; lean_object* v_newLetDecls_3019_; lean_object* v_nextExprIdx_3020_; lean_object* v_exprMVarArgs_3021_; lean_object* v_exprFVarArgs_3022_; lean_object* v_toProcess_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3042_; 
v___x_3010_ = lean_st_ref_take(v_a_3002_);
v_lctx_3011_ = lean_ctor_get(v_a_3003_, 2);
v_visitedLevel_3012_ = lean_ctor_get(v___x_3010_, 0);
v_visitedExpr_3013_ = lean_ctor_get(v___x_3010_, 1);
v_levelParams_3014_ = lean_ctor_get(v___x_3010_, 2);
v_nextLevelIdx_3015_ = lean_ctor_get(v___x_3010_, 3);
v_levelArgs_3016_ = lean_ctor_get(v___x_3010_, 4);
v_newLocalDecls_3017_ = lean_ctor_get(v___x_3010_, 5);
v_newLocalDeclsForMVars_3018_ = lean_ctor_get(v___x_3010_, 6);
v_newLetDecls_3019_ = lean_ctor_get(v___x_3010_, 7);
v_nextExprIdx_3020_ = lean_ctor_get(v___x_3010_, 8);
v_exprMVarArgs_3021_ = lean_ctor_get(v___x_3010_, 9);
v_exprFVarArgs_3022_ = lean_ctor_get(v___x_3010_, 10);
v_toProcess_3023_ = lean_ctor_get(v___x_3010_, 11);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3025_ = v___x_3010_;
v_isShared_3026_ = v_isSharedCheck_3042_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_toProcess_3023_);
lean_inc(v_exprFVarArgs_3022_);
lean_inc(v_exprMVarArgs_3021_);
lean_inc(v_nextExprIdx_3020_);
lean_inc(v_newLetDecls_3019_);
lean_inc(v_newLocalDeclsForMVars_3018_);
lean_inc(v_newLocalDecls_3017_);
lean_inc(v_levelArgs_3016_);
lean_inc(v_nextLevelIdx_3015_);
lean_inc(v_levelParams_3014_);
lean_inc(v_visitedExpr_3013_);
lean_inc(v_visitedLevel_3012_);
lean_dec(v___x_3010_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3042_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v_fst_3034_; lean_object* v_snd_3035_; lean_object* v___x_3037_; 
v___x_3027_ = ((lean_object*)(l_Lean_Meta_Closure_instInhabitedToProcessElement_default));
v___x_3028_ = lean_array_get_size(v_toProcess_3023_);
v___x_3029_ = lean_unsigned_to_nat(1u);
v___x_3030_ = lean_nat_sub(v___x_3028_, v___x_3029_);
v___x_3031_ = lean_array_get(v___x_3027_, v_toProcess_3023_, v___x_3030_);
lean_dec(v___x_3030_);
v___x_3032_ = lean_array_pop(v_toProcess_3023_);
lean_inc_ref(v_lctx_3011_);
v___x_3033_ = l_Lean_Meta_Closure_pickNextToProcessAux(v_lctx_3011_, v___x_3008_, v___x_3032_, v___x_3031_);
v_fst_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_fst_3034_);
v_snd_3035_ = lean_ctor_get(v___x_3033_, 1);
lean_inc(v_snd_3035_);
lean_dec_ref(v___x_3033_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 11, v_snd_3035_);
v___x_3037_ = v___x_3025_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_visitedLevel_3012_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_visitedExpr_3013_);
lean_ctor_set(v_reuseFailAlloc_3041_, 2, v_levelParams_3014_);
lean_ctor_set(v_reuseFailAlloc_3041_, 3, v_nextLevelIdx_3015_);
lean_ctor_set(v_reuseFailAlloc_3041_, 4, v_levelArgs_3016_);
lean_ctor_set(v_reuseFailAlloc_3041_, 5, v_newLocalDecls_3017_);
lean_ctor_set(v_reuseFailAlloc_3041_, 6, v_newLocalDeclsForMVars_3018_);
lean_ctor_set(v_reuseFailAlloc_3041_, 7, v_newLetDecls_3019_);
lean_ctor_set(v_reuseFailAlloc_3041_, 8, v_nextExprIdx_3020_);
lean_ctor_set(v_reuseFailAlloc_3041_, 9, v_exprMVarArgs_3021_);
lean_ctor_set(v_reuseFailAlloc_3041_, 10, v_exprFVarArgs_3022_);
lean_ctor_set(v_reuseFailAlloc_3041_, 11, v_snd_3035_);
v___x_3037_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3038_ = lean_st_ref_put(v_a_3002_, v___x_3037_);
v___x_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_fst_3034_);
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
return v___x_3040_;
}
}
}
else
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_box(0);
v___x_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_3045_, v_a_3046_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_3050_, v_a_3051_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
uint8_t v_a_boxed_3064_; lean_object* v_res_3065_; 
v_a_boxed_3064_ = lean_unbox(v_a_3057_);
v_res_3065_ = l_Lean_Meta_Closure_pickNextToProcess_x3f(v_a_boxed_3064_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec(v_a_3058_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object* v_e_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v___x_3069_; lean_object* v_visitedLevel_3070_; lean_object* v_visitedExpr_3071_; lean_object* v_levelParams_3072_; lean_object* v_nextLevelIdx_3073_; lean_object* v_levelArgs_3074_; lean_object* v_newLocalDecls_3075_; lean_object* v_newLocalDeclsForMVars_3076_; lean_object* v_newLetDecls_3077_; lean_object* v_nextExprIdx_3078_; lean_object* v_exprMVarArgs_3079_; lean_object* v_exprFVarArgs_3080_; lean_object* v_toProcess_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3092_; 
v___x_3069_ = lean_st_ref_take(v_a_3067_);
v_visitedLevel_3070_ = lean_ctor_get(v___x_3069_, 0);
v_visitedExpr_3071_ = lean_ctor_get(v___x_3069_, 1);
v_levelParams_3072_ = lean_ctor_get(v___x_3069_, 2);
v_nextLevelIdx_3073_ = lean_ctor_get(v___x_3069_, 3);
v_levelArgs_3074_ = lean_ctor_get(v___x_3069_, 4);
v_newLocalDecls_3075_ = lean_ctor_get(v___x_3069_, 5);
v_newLocalDeclsForMVars_3076_ = lean_ctor_get(v___x_3069_, 6);
v_newLetDecls_3077_ = lean_ctor_get(v___x_3069_, 7);
v_nextExprIdx_3078_ = lean_ctor_get(v___x_3069_, 8);
v_exprMVarArgs_3079_ = lean_ctor_get(v___x_3069_, 9);
v_exprFVarArgs_3080_ = lean_ctor_get(v___x_3069_, 10);
v_toProcess_3081_ = lean_ctor_get(v___x_3069_, 11);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3083_ = v___x_3069_;
v_isShared_3084_ = v_isSharedCheck_3092_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_toProcess_3081_);
lean_inc(v_exprFVarArgs_3080_);
lean_inc(v_exprMVarArgs_3079_);
lean_inc(v_nextExprIdx_3078_);
lean_inc(v_newLetDecls_3077_);
lean_inc(v_newLocalDeclsForMVars_3076_);
lean_inc(v_newLocalDecls_3075_);
lean_inc(v_levelArgs_3074_);
lean_inc(v_nextLevelIdx_3073_);
lean_inc(v_levelParams_3072_);
lean_inc(v_visitedExpr_3071_);
lean_inc(v_visitedLevel_3070_);
lean_dec(v___x_3069_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3092_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3085_ = lean_array_push(v_exprFVarArgs_3080_, v_e_3066_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 10, v___x_3085_);
v___x_3087_ = v___x_3083_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_visitedLevel_3070_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_visitedExpr_3071_);
lean_ctor_set(v_reuseFailAlloc_3091_, 2, v_levelParams_3072_);
lean_ctor_set(v_reuseFailAlloc_3091_, 3, v_nextLevelIdx_3073_);
lean_ctor_set(v_reuseFailAlloc_3091_, 4, v_levelArgs_3074_);
lean_ctor_set(v_reuseFailAlloc_3091_, 5, v_newLocalDecls_3075_);
lean_ctor_set(v_reuseFailAlloc_3091_, 6, v_newLocalDeclsForMVars_3076_);
lean_ctor_set(v_reuseFailAlloc_3091_, 7, v_newLetDecls_3077_);
lean_ctor_set(v_reuseFailAlloc_3091_, 8, v_nextExprIdx_3078_);
lean_ctor_set(v_reuseFailAlloc_3091_, 9, v_exprMVarArgs_3079_);
lean_ctor_set(v_reuseFailAlloc_3091_, 10, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3091_, 11, v_toProcess_3081_);
v___x_3087_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = lean_st_ref_put(v_a_3067_, v___x_3087_);
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
return v___x_3090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object* v_e_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_3093_, v_a_3094_);
lean_dec(v_a_3094_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* v_e_3097_, uint8_t v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_3097_, v_a_3099_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* v_e_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
uint8_t v_a_boxed_3114_; lean_object* v_res_3115_; 
v_a_boxed_3114_ = lean_unbox(v_a_3107_);
v_res_3115_ = l_Lean_Meta_Closure_pushFVarArg(v_e_3106_, v_a_boxed_3114_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
lean_dec(v_a_3108_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* v_newFVarId_3116_, lean_object* v_userName_3117_, lean_object* v_type_3118_, uint8_t v_bi_3119_, uint8_t v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lean_Meta_Closure_collectExpr(v_type_3118_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3161_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3161_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3161_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v_visitedLevel_3133_; lean_object* v_visitedExpr_3134_; lean_object* v_levelParams_3135_; lean_object* v_nextLevelIdx_3136_; lean_object* v_levelArgs_3137_; lean_object* v_newLocalDecls_3138_; lean_object* v_newLocalDeclsForMVars_3139_; lean_object* v_newLetDecls_3140_; lean_object* v_nextExprIdx_3141_; lean_object* v_exprMVarArgs_3142_; lean_object* v_exprFVarArgs_3143_; lean_object* v_toProcess_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3160_; 
v___x_3132_ = lean_st_ref_take(v_a_3121_);
v_visitedLevel_3133_ = lean_ctor_get(v___x_3132_, 0);
v_visitedExpr_3134_ = lean_ctor_get(v___x_3132_, 1);
v_levelParams_3135_ = lean_ctor_get(v___x_3132_, 2);
v_nextLevelIdx_3136_ = lean_ctor_get(v___x_3132_, 3);
v_levelArgs_3137_ = lean_ctor_get(v___x_3132_, 4);
v_newLocalDecls_3138_ = lean_ctor_get(v___x_3132_, 5);
v_newLocalDeclsForMVars_3139_ = lean_ctor_get(v___x_3132_, 6);
v_newLetDecls_3140_ = lean_ctor_get(v___x_3132_, 7);
v_nextExprIdx_3141_ = lean_ctor_get(v___x_3132_, 8);
v_exprMVarArgs_3142_ = lean_ctor_get(v___x_3132_, 9);
v_exprFVarArgs_3143_ = lean_ctor_get(v___x_3132_, 10);
v_toProcess_3144_ = lean_ctor_get(v___x_3132_, 11);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3146_ = v___x_3132_;
v_isShared_3147_ = v_isSharedCheck_3160_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_toProcess_3144_);
lean_inc(v_exprFVarArgs_3143_);
lean_inc(v_exprMVarArgs_3142_);
lean_inc(v_nextExprIdx_3141_);
lean_inc(v_newLetDecls_3140_);
lean_inc(v_newLocalDeclsForMVars_3139_);
lean_inc(v_newLocalDecls_3138_);
lean_inc(v_levelArgs_3137_);
lean_inc(v_nextLevelIdx_3136_);
lean_inc(v_levelParams_3135_);
lean_inc(v_visitedExpr_3134_);
lean_inc(v_visitedLevel_3133_);
lean_dec(v___x_3132_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3160_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3153_; 
v___x_3148_ = lean_unsigned_to_nat(0u);
v___x_3149_ = 0;
v___x_3150_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3150_, 0, v___x_3148_);
lean_ctor_set(v___x_3150_, 1, v_newFVarId_3116_);
lean_ctor_set(v___x_3150_, 2, v_userName_3117_);
lean_ctor_set(v___x_3150_, 3, v_a_3128_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*4, v_bi_3119_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*4 + 1, v___x_3149_);
v___x_3151_ = lean_array_push(v_newLocalDecls_3138_, v___x_3150_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 5, v___x_3151_);
v___x_3153_ = v___x_3146_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_visitedLevel_3133_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_visitedExpr_3134_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_levelParams_3135_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_nextLevelIdx_3136_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_levelArgs_3137_);
lean_ctor_set(v_reuseFailAlloc_3159_, 5, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3159_, 6, v_newLocalDeclsForMVars_3139_);
lean_ctor_set(v_reuseFailAlloc_3159_, 7, v_newLetDecls_3140_);
lean_ctor_set(v_reuseFailAlloc_3159_, 8, v_nextExprIdx_3141_);
lean_ctor_set(v_reuseFailAlloc_3159_, 9, v_exprMVarArgs_3142_);
lean_ctor_set(v_reuseFailAlloc_3159_, 10, v_exprFVarArgs_3143_);
lean_ctor_set(v_reuseFailAlloc_3159_, 11, v_toProcess_3144_);
v___x_3153_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3154_ = lean_st_ref_put(v_a_3121_, v___x_3153_);
v___x_3155_ = lean_box(0);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3155_);
v___x_3157_ = v___x_3130_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v_userName_3117_);
lean_dec(v_newFVarId_3116_);
v_a_3162_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3127_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3127_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* v_newFVarId_3170_, lean_object* v_userName_3171_, lean_object* v_type_3172_, lean_object* v_bi_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_){
_start:
{
uint8_t v_bi_boxed_3181_; uint8_t v_a_boxed_3182_; lean_object* v_res_3183_; 
v_bi_boxed_3181_ = lean_unbox(v_bi_3173_);
v_a_boxed_3182_ = lean_unbox(v_a_3174_);
v_res_3183_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_3170_, v_userName_3171_, v_type_3172_, v_bi_boxed_3181_, v_a_boxed_3182_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
return v_res_3183_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(lean_object* v_k_3184_, lean_object* v_t_3185_){
_start:
{
if (lean_obj_tag(v_t_3185_) == 0)
{
lean_object* v_k_3186_; lean_object* v_l_3187_; lean_object* v_r_3188_; uint8_t v___x_3189_; 
v_k_3186_ = lean_ctor_get(v_t_3185_, 1);
v_l_3187_ = lean_ctor_get(v_t_3185_, 3);
v_r_3188_ = lean_ctor_get(v_t_3185_, 4);
v___x_3189_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3184_, v_k_3186_);
switch(v___x_3189_)
{
case 0:
{
v_t_3185_ = v_l_3187_;
goto _start;
}
case 1:
{
uint8_t v___x_3191_; 
v___x_3191_ = 1;
return v___x_3191_;
}
default: 
{
v_t_3185_ = v_r_3188_;
goto _start;
}
}
}
else
{
uint8_t v___x_3193_; 
v___x_3193_ = 0;
return v___x_3193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object* v_k_3194_, lean_object* v_t_3195_){
_start:
{
uint8_t v_res_3196_; lean_object* v_r_3197_; 
v_res_3196_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_3194_, v_t_3195_);
lean_dec(v_t_3195_);
lean_dec(v_k_3194_);
v_r_3197_ = lean_box(v_res_3196_);
return v_r_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(lean_object* v_newFVarId_3198_, lean_object* v_a_3199_, size_t v_sz_3200_, size_t v_i_3201_, lean_object* v_bs_3202_){
_start:
{
uint8_t v___x_3203_; 
v___x_3203_ = lean_usize_dec_lt(v_i_3201_, v_sz_3200_);
if (v___x_3203_ == 0)
{
lean_dec(v_newFVarId_3198_);
return v_bs_3202_;
}
else
{
lean_object* v_v_3204_; lean_object* v___x_3205_; lean_object* v_bs_x27_3206_; lean_object* v___x_3207_; size_t v___x_3208_; size_t v___x_3209_; lean_object* v___x_3210_; 
v_v_3204_ = lean_array_uget(v_bs_3202_, v_i_3201_);
v___x_3205_ = lean_unsigned_to_nat(0u);
v_bs_x27_3206_ = lean_array_uset(v_bs_3202_, v_i_3201_, v___x_3205_);
lean_inc(v_newFVarId_3198_);
v___x_3207_ = l_Lean_LocalDecl_replaceFVarId(v_newFVarId_3198_, v_a_3199_, v_v_3204_);
v___x_3208_ = ((size_t)1ULL);
v___x_3209_ = lean_usize_add(v_i_3201_, v___x_3208_);
v___x_3210_ = lean_array_uset(v_bs_x27_3206_, v_i_3201_, v___x_3207_);
v_i_3201_ = v___x_3209_;
v_bs_3202_ = v___x_3210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(lean_object* v_newFVarId_3212_, lean_object* v_a_3213_, lean_object* v_sz_3214_, lean_object* v_i_3215_, lean_object* v_bs_3216_){
_start:
{
size_t v_sz_boxed_3217_; size_t v_i_boxed_3218_; lean_object* v_res_3219_; 
v_sz_boxed_3217_ = lean_unbox_usize(v_sz_3214_);
lean_dec(v_sz_3214_);
v_i_boxed_3218_ = lean_unbox_usize(v_i_3215_);
lean_dec(v_i_3215_);
v_res_3219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_3212_, v_a_3213_, v_sz_boxed_3217_, v_i_boxed_3218_, v_bs_3216_);
lean_dec_ref(v_a_3213_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_3221_, v_a_3222_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3355_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3230_ = v___x_3227_;
v_isShared_3231_ = v_isSharedCheck_3355_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3355_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
if (lean_obj_tag(v_a_3228_) == 0)
{
lean_object* v___x_3232_; lean_object* v___x_3234_; 
v___x_3232_ = lean_box(0);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v___x_3232_);
v___x_3234_ = v___x_3230_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
else
{
lean_object* v_val_3236_; lean_object* v_fvarId_3237_; lean_object* v_newFVarId_3238_; lean_object* v___x_3239_; 
lean_del_object(v___x_3230_);
v_val_3236_ = lean_ctor_get(v_a_3228_, 0);
lean_inc(v_val_3236_);
lean_dec_ref_known(v_a_3228_, 1);
v_fvarId_3237_ = lean_ctor_get(v_val_3236_, 0);
lean_inc_n(v_fvarId_3237_, 2);
v_newFVarId_3238_ = lean_ctor_get(v_val_3236_, 1);
lean_inc(v_newFVarId_3238_);
lean_dec(v_val_3236_);
v___x_3239_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_3237_, v_a_3222_, v_a_3224_, v_a_3225_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref_known(v___x_3239_, 1);
if (lean_obj_tag(v_a_3240_) == 0)
{
lean_object* v_userName_3241_; lean_object* v_type_3242_; uint8_t v_bi_3243_; lean_object* v___x_3244_; 
v_userName_3241_ = lean_ctor_get(v_a_3240_, 2);
lean_inc(v_userName_3241_);
v_type_3242_ = lean_ctor_get(v_a_3240_, 3);
lean_inc_ref(v_type_3242_);
v_bi_3243_ = lean_ctor_get_uint8(v_a_3240_, sizeof(void*)*4);
lean_dec_ref_known(v_a_3240_, 4);
v___x_3244_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_3238_, v_userName_3241_, v_type_3242_, v_bi_3243_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
lean_dec_ref_known(v___x_3244_, 1);
v___x_3245_ = l_Lean_mkFVar(v_fvarId_3237_);
v___x_3246_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_3245_, v_a_3221_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_dec_ref_known(v___x_3246_, 1);
goto _start;
}
else
{
return v___x_3246_;
}
}
else
{
lean_dec(v_fvarId_3237_);
return v___x_3244_;
}
}
else
{
lean_object* v_userName_3248_; lean_object* v_type_3249_; lean_object* v_value_3250_; uint8_t v_nondep_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3344_; 
v_userName_3248_ = lean_ctor_get(v_a_3240_, 2);
v_type_3249_ = lean_ctor_get(v_a_3240_, 3);
v_value_3250_ = lean_ctor_get(v_a_3240_, 4);
v_nondep_3251_ = lean_ctor_get_uint8(v_a_3240_, sizeof(void*)*5);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_a_3240_);
if (v_isSharedCheck_3344_ == 0)
{
lean_object* v_unused_3345_; lean_object* v_unused_3346_; 
v_unused_3345_ = lean_ctor_get(v_a_3240_, 1);
lean_dec(v_unused_3345_);
v_unused_3346_ = lean_ctor_get(v_a_3240_, 0);
lean_dec(v_unused_3346_);
v___x_3253_ = v_a_3240_;
v_isShared_3254_ = v_isSharedCheck_3344_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_value_3250_);
lean_inc(v_type_3249_);
lean_inc(v_userName_3248_);
lean_dec(v_a_3240_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3344_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v_a_3223_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref_known(v___x_3255_, 1);
if (v_nondep_3251_ == 0)
{
uint8_t v___x_3263_; 
v___x_3263_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_fvarId_3237_, v_a_3256_);
lean_dec(v_a_3256_);
if (v___x_3263_ == 0)
{
lean_del_object(v___x_3253_);
lean_dec_ref(v_value_3250_);
goto v___jp_3257_;
}
else
{
lean_object* v___x_3264_; 
lean_dec(v_fvarId_3237_);
v___x_3264_ = l_Lean_Meta_Closure_collectExpr(v_type_3249_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v___x_3266_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref_known(v___x_3264_, 1);
v___x_3266_ = l_Lean_Meta_Closure_collectExpr(v_value_3250_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; lean_object* v_visitedLevel_3269_; lean_object* v_visitedExpr_3270_; lean_object* v_levelParams_3271_; lean_object* v_nextLevelIdx_3272_; lean_object* v_levelArgs_3273_; lean_object* v_newLocalDecls_3274_; lean_object* v_newLocalDeclsForMVars_3275_; lean_object* v_newLetDecls_3276_; lean_object* v_nextExprIdx_3277_; lean_object* v_exprMVarArgs_3278_; lean_object* v_exprFVarArgs_3279_; lean_object* v_toProcess_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3319_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v___x_3266_, 1);
v___x_3268_ = lean_st_ref_take(v_a_3221_);
v_visitedLevel_3269_ = lean_ctor_get(v___x_3268_, 0);
v_visitedExpr_3270_ = lean_ctor_get(v___x_3268_, 1);
v_levelParams_3271_ = lean_ctor_get(v___x_3268_, 2);
v_nextLevelIdx_3272_ = lean_ctor_get(v___x_3268_, 3);
v_levelArgs_3273_ = lean_ctor_get(v___x_3268_, 4);
v_newLocalDecls_3274_ = lean_ctor_get(v___x_3268_, 5);
v_newLocalDeclsForMVars_3275_ = lean_ctor_get(v___x_3268_, 6);
v_newLetDecls_3276_ = lean_ctor_get(v___x_3268_, 7);
v_nextExprIdx_3277_ = lean_ctor_get(v___x_3268_, 8);
v_exprMVarArgs_3278_ = lean_ctor_get(v___x_3268_, 9);
v_exprFVarArgs_3279_ = lean_ctor_get(v___x_3268_, 10);
v_toProcess_3280_ = lean_ctor_get(v___x_3268_, 11);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3282_ = v___x_3268_;
v_isShared_3283_ = v_isSharedCheck_3319_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_toProcess_3280_);
lean_inc(v_exprFVarArgs_3279_);
lean_inc(v_exprMVarArgs_3278_);
lean_inc(v_nextExprIdx_3277_);
lean_inc(v_newLetDecls_3276_);
lean_inc(v_newLocalDeclsForMVars_3275_);
lean_inc(v_newLocalDecls_3274_);
lean_inc(v_levelArgs_3273_);
lean_inc(v_nextLevelIdx_3272_);
lean_inc(v_levelParams_3271_);
lean_inc(v_visitedExpr_3270_);
lean_inc(v_visitedLevel_3269_);
lean_dec(v___x_3268_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3319_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; uint8_t v___x_3285_; lean_object* v___x_3287_; 
v___x_3284_ = lean_unsigned_to_nat(0u);
v___x_3285_ = 0;
lean_inc(v_a_3267_);
lean_inc(v_newFVarId_3238_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 4, v_a_3267_);
lean_ctor_set(v___x_3253_, 3, v_a_3265_);
lean_ctor_set(v___x_3253_, 1, v_newFVarId_3238_);
lean_ctor_set(v___x_3253_, 0, v___x_3284_);
v___x_3287_ = v___x_3253_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3284_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v_newFVarId_3238_);
lean_ctor_set(v_reuseFailAlloc_3318_, 2, v_userName_3248_);
lean_ctor_set(v_reuseFailAlloc_3318_, 3, v_a_3265_);
lean_ctor_set(v_reuseFailAlloc_3318_, 4, v_a_3267_);
lean_ctor_set_uint8(v_reuseFailAlloc_3318_, sizeof(void*)*5, v_nondep_3251_);
v___x_3287_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
lean_object* v___x_3288_; lean_object* v___x_3290_; 
lean_ctor_set_uint8(v___x_3287_, sizeof(void*)*5 + 1, v___x_3285_);
v___x_3288_ = lean_array_push(v_newLetDecls_3276_, v___x_3287_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 7, v___x_3288_);
v___x_3290_ = v___x_3282_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_visitedLevel_3269_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_visitedExpr_3270_);
lean_ctor_set(v_reuseFailAlloc_3317_, 2, v_levelParams_3271_);
lean_ctor_set(v_reuseFailAlloc_3317_, 3, v_nextLevelIdx_3272_);
lean_ctor_set(v_reuseFailAlloc_3317_, 4, v_levelArgs_3273_);
lean_ctor_set(v_reuseFailAlloc_3317_, 5, v_newLocalDecls_3274_);
lean_ctor_set(v_reuseFailAlloc_3317_, 6, v_newLocalDeclsForMVars_3275_);
lean_ctor_set(v_reuseFailAlloc_3317_, 7, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3317_, 8, v_nextExprIdx_3277_);
lean_ctor_set(v_reuseFailAlloc_3317_, 9, v_exprMVarArgs_3278_);
lean_ctor_set(v_reuseFailAlloc_3317_, 10, v_exprFVarArgs_3279_);
lean_ctor_set(v_reuseFailAlloc_3317_, 11, v_toProcess_3280_);
v___x_3290_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v_visitedLevel_3293_; lean_object* v_visitedExpr_3294_; lean_object* v_levelParams_3295_; lean_object* v_nextLevelIdx_3296_; lean_object* v_levelArgs_3297_; lean_object* v_newLocalDecls_3298_; lean_object* v_newLocalDeclsForMVars_3299_; lean_object* v_newLetDecls_3300_; lean_object* v_nextExprIdx_3301_; lean_object* v_exprMVarArgs_3302_; lean_object* v_exprFVarArgs_3303_; lean_object* v_toProcess_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3316_; 
v___x_3291_ = lean_st_ref_put(v_a_3221_, v___x_3290_);
v___x_3292_ = lean_st_ref_take(v_a_3221_);
v_visitedLevel_3293_ = lean_ctor_get(v___x_3292_, 0);
v_visitedExpr_3294_ = lean_ctor_get(v___x_3292_, 1);
v_levelParams_3295_ = lean_ctor_get(v___x_3292_, 2);
v_nextLevelIdx_3296_ = lean_ctor_get(v___x_3292_, 3);
v_levelArgs_3297_ = lean_ctor_get(v___x_3292_, 4);
v_newLocalDecls_3298_ = lean_ctor_get(v___x_3292_, 5);
v_newLocalDeclsForMVars_3299_ = lean_ctor_get(v___x_3292_, 6);
v_newLetDecls_3300_ = lean_ctor_get(v___x_3292_, 7);
v_nextExprIdx_3301_ = lean_ctor_get(v___x_3292_, 8);
v_exprMVarArgs_3302_ = lean_ctor_get(v___x_3292_, 9);
v_exprFVarArgs_3303_ = lean_ctor_get(v___x_3292_, 10);
v_toProcess_3304_ = lean_ctor_get(v___x_3292_, 11);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3306_ = v___x_3292_;
v_isShared_3307_ = v_isSharedCheck_3316_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_toProcess_3304_);
lean_inc(v_exprFVarArgs_3303_);
lean_inc(v_exprMVarArgs_3302_);
lean_inc(v_nextExprIdx_3301_);
lean_inc(v_newLetDecls_3300_);
lean_inc(v_newLocalDeclsForMVars_3299_);
lean_inc(v_newLocalDecls_3298_);
lean_inc(v_levelArgs_3297_);
lean_inc(v_nextLevelIdx_3296_);
lean_inc(v_levelParams_3295_);
lean_inc(v_visitedExpr_3294_);
lean_inc(v_visitedLevel_3293_);
lean_dec(v___x_3292_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3316_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
size_t v_sz_3308_; size_t v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v_sz_3308_ = lean_array_size(v_newLocalDecls_3298_);
v___x_3309_ = ((size_t)0ULL);
v___x_3310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_3238_, v_a_3267_, v_sz_3308_, v___x_3309_, v_newLocalDecls_3298_);
lean_dec(v_a_3267_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 5, v___x_3310_);
v___x_3312_ = v___x_3306_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_visitedLevel_3293_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_visitedExpr_3294_);
lean_ctor_set(v_reuseFailAlloc_3315_, 2, v_levelParams_3295_);
lean_ctor_set(v_reuseFailAlloc_3315_, 3, v_nextLevelIdx_3296_);
lean_ctor_set(v_reuseFailAlloc_3315_, 4, v_levelArgs_3297_);
lean_ctor_set(v_reuseFailAlloc_3315_, 5, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3315_, 6, v_newLocalDeclsForMVars_3299_);
lean_ctor_set(v_reuseFailAlloc_3315_, 7, v_newLetDecls_3300_);
lean_ctor_set(v_reuseFailAlloc_3315_, 8, v_nextExprIdx_3301_);
lean_ctor_set(v_reuseFailAlloc_3315_, 9, v_exprMVarArgs_3302_);
lean_ctor_set(v_reuseFailAlloc_3315_, 10, v_exprFVarArgs_3303_);
lean_ctor_set(v_reuseFailAlloc_3315_, 11, v_toProcess_3304_);
v___x_3312_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
lean_object* v___x_3313_; 
v___x_3313_ = lean_st_ref_put(v_a_3221_, v___x_3312_);
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec(v_a_3265_);
lean_del_object(v___x_3253_);
lean_dec(v_userName_3248_);
lean_dec(v_newFVarId_3238_);
v_a_3320_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3266_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3266_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_del_object(v___x_3253_);
lean_dec_ref(v_value_3250_);
lean_dec(v_userName_3248_);
lean_dec(v_newFVarId_3238_);
v_a_3328_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3264_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3264_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
}
else
{
lean_dec(v_a_3256_);
lean_del_object(v___x_3253_);
lean_dec_ref(v_value_3250_);
goto v___jp_3257_;
}
v___jp_3257_:
{
uint8_t v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = 0;
v___x_3259_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_3238_, v_userName_3248_, v_type_3249_, v___x_3258_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec_ref_known(v___x_3259_, 1);
v___x_3260_ = l_Lean_mkFVar(v_fvarId_3237_);
v___x_3261_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_3260_, v_a_3221_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_dec_ref_known(v___x_3261_, 1);
goto _start;
}
else
{
return v___x_3261_;
}
}
else
{
lean_dec(v_fvarId_3237_);
return v___x_3259_;
}
}
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_del_object(v___x_3253_);
lean_dec_ref(v_value_3250_);
lean_dec_ref(v_type_3249_);
lean_dec(v_userName_3248_);
lean_dec(v_newFVarId_3238_);
lean_dec(v_fvarId_3237_);
v_a_3336_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3255_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3255_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec(v_newFVarId_3238_);
lean_dec(v_fvarId_3237_);
v_a_3347_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3239_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3239_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
v_a_3356_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3227_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3227_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
uint8_t v_a_boxed_3371_; lean_object* v_res_3372_; 
v_a_boxed_3371_ = lean_unbox(v_a_3364_);
v_res_3372_ = l_Lean_Meta_Closure_process(v_a_boxed_3371_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
lean_dec(v_a_3365_);
return v_res_3372_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(lean_object* v_00_u03b2_3373_, lean_object* v_k_3374_, lean_object* v_t_3375_){
_start:
{
uint8_t v___x_3376_; 
v___x_3376_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_3374_, v_t_3375_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___boxed(lean_object* v_00_u03b2_3377_, lean_object* v_k_3378_, lean_object* v_t_3379_){
_start:
{
uint8_t v_res_3380_; lean_object* v_r_3381_; 
v_res_3380_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(v_00_u03b2_3377_, v_k_3378_, v_t_3379_);
lean_dec(v_t_3379_);
lean_dec(v_k_3378_);
v_r_3381_ = lean_box(v_res_3380_);
return v_r_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object* v_decls_3382_, lean_object* v_xs_3383_, uint8_t v_isLambda_3384_, lean_object* v_i_3385_, lean_object* v_x_3386_, lean_object* v_b_3387_){
_start:
{
lean_object* v_decl_3388_; 
v_decl_3388_ = lean_array_fget_borrowed(v_decls_3382_, v_i_3385_);
if (lean_obj_tag(v_decl_3388_) == 0)
{
lean_object* v_userName_3389_; lean_object* v_type_3390_; uint8_t v_bi_3391_; lean_object* v_ty_3392_; 
v_userName_3389_ = lean_ctor_get(v_decl_3388_, 2);
v_type_3390_ = lean_ctor_get(v_decl_3388_, 3);
v_bi_3391_ = lean_ctor_get_uint8(v_decl_3388_, sizeof(void*)*4);
v_ty_3392_ = lean_expr_abstract_range(v_type_3390_, v_i_3385_, v_xs_3383_);
if (v_isLambda_3384_ == 0)
{
lean_object* v___x_3393_; 
lean_inc(v_userName_3389_);
v___x_3393_ = l_Lean_mkForall(v_userName_3389_, v_bi_3391_, v_ty_3392_, v_b_3387_);
return v___x_3393_;
}
else
{
lean_object* v___x_3394_; 
lean_inc(v_userName_3389_);
v___x_3394_ = l_Lean_mkLambda(v_userName_3389_, v_bi_3391_, v_ty_3392_, v_b_3387_);
return v___x_3394_;
}
}
else
{
lean_object* v_userName_3395_; lean_object* v_type_3396_; lean_object* v_value_3397_; uint8_t v_nondep_3398_; lean_object* v___x_3399_; uint8_t v___x_3400_; 
v_userName_3395_ = lean_ctor_get(v_decl_3388_, 2);
v_type_3396_ = lean_ctor_get(v_decl_3388_, 3);
v_value_3397_ = lean_ctor_get(v_decl_3388_, 4);
v_nondep_3398_ = lean_ctor_get_uint8(v_decl_3388_, sizeof(void*)*5);
v___x_3399_ = lean_unsigned_to_nat(0u);
v___x_3400_ = lean_expr_has_loose_bvar(v_b_3387_, v___x_3399_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = lean_unsigned_to_nat(1u);
v___x_3402_ = lean_expr_lower_loose_bvars(v_b_3387_, v___x_3401_, v___x_3401_);
lean_dec_ref(v_b_3387_);
return v___x_3402_;
}
else
{
lean_object* v_ty_3403_; lean_object* v_val_3404_; lean_object* v___x_3405_; 
v_ty_3403_ = lean_expr_abstract_range(v_type_3396_, v_i_3385_, v_xs_3383_);
v_val_3404_ = lean_expr_abstract_range(v_value_3397_, v_i_3385_, v_xs_3383_);
lean_inc(v_userName_3395_);
v___x_3405_ = l_Lean_Expr_letE___override(v_userName_3395_, v_ty_3403_, v_val_3404_, v_b_3387_, v_nondep_3398_);
return v___x_3405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object* v_decls_3406_, lean_object* v_xs_3407_, lean_object* v_isLambda_3408_, lean_object* v_i_3409_, lean_object* v_x_3410_, lean_object* v_b_3411_){
_start:
{
uint8_t v_isLambda_boxed_3412_; lean_object* v_res_3413_; 
v_isLambda_boxed_3412_ = lean_unbox(v_isLambda_3408_);
v_res_3413_ = l_Lean_Meta_Closure_mkBinding___lam__0(v_decls_3406_, v_xs_3407_, v_isLambda_boxed_3412_, v_i_3409_, v_x_3410_, v_b_3411_);
lean_dec(v_i_3409_);
lean_dec_ref(v_xs_3407_);
lean_dec_ref(v_decls_3406_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t v_isLambda_3434_, lean_object* v_decls_3435_, lean_object* v_b_3436_){
_start:
{
lean_object* v___f_3437_; lean_object* v___x_3438_; size_t v_sz_3439_; size_t v___x_3440_; lean_object* v_xs_3441_; lean_object* v___x_3442_; lean_object* v___f_3443_; lean_object* v_b_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___f_3437_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__0));
v___x_3438_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__10));
v_sz_3439_ = lean_array_size(v_decls_3435_);
v___x_3440_ = ((size_t)0ULL);
lean_inc_ref_n(v_decls_3435_, 2);
v_xs_3441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3438_, v___f_3437_, v_sz_3439_, v___x_3440_, v_decls_3435_);
v___x_3442_ = lean_box(v_isLambda_3434_);
lean_inc(v_xs_3441_);
v___f_3443_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3443_, 0, v_decls_3435_);
lean_closure_set(v___f_3443_, 1, v_xs_3441_);
lean_closure_set(v___f_3443_, 2, v___x_3442_);
v_b_3444_ = lean_expr_abstract(v_b_3436_, v_xs_3441_);
lean_dec(v_xs_3441_);
v___x_3445_ = lean_array_get_size(v_decls_3435_);
lean_dec_ref(v_decls_3435_);
v___x_3446_ = l_Nat_foldRev___redArg(v___x_3445_, v___f_3443_, v_b_3444_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* v_isLambda_3447_, lean_object* v_decls_3448_, lean_object* v_b_3449_){
_start:
{
uint8_t v_isLambda_boxed_3450_; lean_object* v_res_3451_; 
v_isLambda_boxed_3450_ = lean_unbox(v_isLambda_3447_);
v_res_3451_ = l_Lean_Meta_Closure_mkBinding(v_isLambda_boxed_3450_, v_decls_3448_, v_b_3449_);
lean_dec_ref(v_b_3449_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(size_t v_sz_3452_, size_t v_i_3453_, lean_object* v_bs_3454_){
_start:
{
uint8_t v___x_3455_; 
v___x_3455_ = lean_usize_dec_lt(v_i_3453_, v_sz_3452_);
if (v___x_3455_ == 0)
{
return v_bs_3454_;
}
else
{
lean_object* v_v_3456_; lean_object* v___x_3457_; lean_object* v_bs_x27_3458_; lean_object* v___x_3459_; size_t v___x_3460_; size_t v___x_3461_; lean_object* v___x_3462_; 
v_v_3456_ = lean_array_uget(v_bs_3454_, v_i_3453_);
v___x_3457_ = lean_unsigned_to_nat(0u);
v_bs_x27_3458_ = lean_array_uset(v_bs_3454_, v_i_3453_, v___x_3457_);
v___x_3459_ = l_Lean_LocalDecl_toExpr(v_v_3456_);
v___x_3460_ = ((size_t)1ULL);
v___x_3461_ = lean_usize_add(v_i_3453_, v___x_3460_);
v___x_3462_ = lean_array_uset(v_bs_x27_3458_, v_i_3453_, v___x_3459_);
v_i_3453_ = v___x_3461_;
v_bs_3454_ = v___x_3462_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object* v_sz_3464_, lean_object* v_i_3465_, lean_object* v_bs_3466_){
_start:
{
size_t v_sz_boxed_3467_; size_t v_i_boxed_3468_; lean_object* v_res_3469_; 
v_sz_boxed_3467_ = lean_unbox_usize(v_sz_3464_);
lean_dec(v_sz_3464_);
v_i_boxed_3468_ = lean_unbox_usize(v_i_3465_);
lean_dec(v_i_3465_);
v_res_3469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_boxed_3467_, v_i_boxed_3468_, v_bs_3466_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object* v_decls_3470_, lean_object* v_xs_3471_, lean_object* v_x_3472_, lean_object* v_x_3473_){
_start:
{
lean_object* v_zero_3474_; uint8_t v_isZero_3475_; 
v_zero_3474_ = lean_unsigned_to_nat(0u);
v_isZero_3475_ = lean_nat_dec_eq(v_x_3472_, v_zero_3474_);
if (v_isZero_3475_ == 1)
{
lean_dec(v_x_3472_);
return v_x_3473_;
}
else
{
lean_object* v_one_3476_; lean_object* v_n_3477_; lean_object* v_decl_3478_; 
v_one_3476_ = lean_unsigned_to_nat(1u);
v_n_3477_ = lean_nat_sub(v_x_3472_, v_one_3476_);
lean_dec(v_x_3472_);
v_decl_3478_ = lean_array_fget_borrowed(v_decls_3470_, v_n_3477_);
if (lean_obj_tag(v_decl_3478_) == 0)
{
lean_object* v_userName_3479_; lean_object* v_type_3480_; uint8_t v_bi_3481_; lean_object* v_ty_3482_; lean_object* v___x_3483_; 
v_userName_3479_ = lean_ctor_get(v_decl_3478_, 2);
v_type_3480_ = lean_ctor_get(v_decl_3478_, 3);
v_bi_3481_ = lean_ctor_get_uint8(v_decl_3478_, sizeof(void*)*4);
v_ty_3482_ = lean_expr_abstract_range(v_type_3480_, v_n_3477_, v_xs_3471_);
lean_inc(v_userName_3479_);
v___x_3483_ = l_Lean_mkLambda(v_userName_3479_, v_bi_3481_, v_ty_3482_, v_x_3473_);
v_x_3472_ = v_n_3477_;
v_x_3473_ = v___x_3483_;
goto _start;
}
else
{
lean_object* v_userName_3485_; lean_object* v_type_3486_; lean_object* v_value_3487_; uint8_t v_nondep_3488_; uint8_t v___x_3489_; 
v_userName_3485_ = lean_ctor_get(v_decl_3478_, 2);
v_type_3486_ = lean_ctor_get(v_decl_3478_, 3);
v_value_3487_ = lean_ctor_get(v_decl_3478_, 4);
v_nondep_3488_ = lean_ctor_get_uint8(v_decl_3478_, sizeof(void*)*5);
v___x_3489_ = lean_expr_has_loose_bvar(v_x_3473_, v_zero_3474_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_expr_lower_loose_bvars(v_x_3473_, v_one_3476_, v_one_3476_);
lean_dec_ref(v_x_3473_);
v_x_3472_ = v_n_3477_;
v_x_3473_ = v___x_3490_;
goto _start;
}
else
{
lean_object* v_ty_3492_; lean_object* v_val_3493_; lean_object* v___x_3494_; 
v_ty_3492_ = lean_expr_abstract_range(v_type_3486_, v_n_3477_, v_xs_3471_);
v_val_3493_ = lean_expr_abstract_range(v_value_3487_, v_n_3477_, v_xs_3471_);
lean_inc(v_userName_3485_);
v___x_3494_ = l_Lean_Expr_letE___override(v_userName_3485_, v_ty_3492_, v_val_3493_, v_x_3473_, v_nondep_3488_);
v_x_3472_ = v_n_3477_;
v_x_3473_ = v___x_3494_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1___boxed(lean_object* v_decls_3496_, lean_object* v_xs_3497_, lean_object* v_x_3498_, lean_object* v_x_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_3496_, v_xs_3497_, v_x_3498_, v_x_3499_);
lean_dec_ref(v_xs_3497_);
lean_dec_ref(v_decls_3496_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(lean_object* v_decls_3501_, lean_object* v_xs_3502_, lean_object* v_x_3503_, lean_object* v_x_3504_){
_start:
{
lean_object* v_zero_3505_; uint8_t v_isZero_3506_; 
v_zero_3505_ = lean_unsigned_to_nat(0u);
v_isZero_3506_ = lean_nat_dec_eq(v_x_3503_, v_zero_3505_);
if (v_isZero_3506_ == 1)
{
return v_x_3504_;
}
else
{
lean_object* v_one_3507_; lean_object* v_n_3508_; lean_object* v_decl_3509_; 
v_one_3507_ = lean_unsigned_to_nat(1u);
v_n_3508_ = lean_nat_sub(v_x_3503_, v_one_3507_);
v_decl_3509_ = lean_array_fget_borrowed(v_decls_3501_, v_n_3508_);
if (lean_obj_tag(v_decl_3509_) == 0)
{
lean_object* v_userName_3510_; lean_object* v_type_3511_; uint8_t v_bi_3512_; lean_object* v_ty_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v_userName_3510_ = lean_ctor_get(v_decl_3509_, 2);
v_type_3511_ = lean_ctor_get(v_decl_3509_, 3);
v_bi_3512_ = lean_ctor_get_uint8(v_decl_3509_, sizeof(void*)*4);
v_ty_3513_ = lean_expr_abstract_range(v_type_3511_, v_n_3508_, v_xs_3502_);
lean_inc(v_userName_3510_);
v___x_3514_ = l_Lean_mkLambda(v_userName_3510_, v_bi_3512_, v_ty_3513_, v_x_3504_);
v___x_3515_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_3501_, v_xs_3502_, v_n_3508_, v___x_3514_);
return v___x_3515_;
}
else
{
lean_object* v_userName_3516_; lean_object* v_type_3517_; lean_object* v_value_3518_; uint8_t v_nondep_3519_; uint8_t v___x_3520_; 
v_userName_3516_ = lean_ctor_get(v_decl_3509_, 2);
v_type_3517_ = lean_ctor_get(v_decl_3509_, 3);
v_value_3518_ = lean_ctor_get(v_decl_3509_, 4);
v_nondep_3519_ = lean_ctor_get_uint8(v_decl_3509_, sizeof(void*)*5);
v___x_3520_ = lean_expr_has_loose_bvar(v_x_3504_, v_zero_3505_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = lean_expr_lower_loose_bvars(v_x_3504_, v_one_3507_, v_one_3507_);
lean_dec_ref(v_x_3504_);
v___x_3522_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_3501_, v_xs_3502_, v_n_3508_, v___x_3521_);
return v___x_3522_;
}
else
{
lean_object* v_ty_3523_; lean_object* v_val_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v_ty_3523_ = lean_expr_abstract_range(v_type_3517_, v_n_3508_, v_xs_3502_);
v_val_3524_ = lean_expr_abstract_range(v_value_3518_, v_n_3508_, v_xs_3502_);
lean_inc(v_userName_3516_);
v___x_3525_ = l_Lean_Expr_letE___override(v_userName_3516_, v_ty_3523_, v_val_3524_, v_x_3504_, v_nondep_3519_);
v___x_3526_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_3501_, v_xs_3502_, v_n_3508_, v___x_3525_);
return v___x_3526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object* v_decls_3527_, lean_object* v_xs_3528_, lean_object* v_x_3529_, lean_object* v_x_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_3527_, v_xs_3528_, v_x_3529_, v_x_3530_);
lean_dec(v_x_3529_);
lean_dec_ref(v_xs_3528_);
lean_dec_ref(v_decls_3527_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* v_decls_3532_, lean_object* v_b_3533_){
_start:
{
size_t v_sz_3534_; size_t v___x_3535_; lean_object* v_xs_3536_; lean_object* v_b_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v_sz_3534_ = lean_array_size(v_decls_3532_);
v___x_3535_ = ((size_t)0ULL);
lean_inc_ref(v_decls_3532_);
v_xs_3536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_3534_, v___x_3535_, v_decls_3532_);
v_b_3537_ = lean_expr_abstract(v_b_3533_, v_xs_3536_);
v___x_3538_ = lean_array_get_size(v_decls_3532_);
v___x_3539_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_3532_, v_xs_3536_, v___x_3538_, v_b_3537_);
lean_dec_ref(v_xs_3536_);
lean_dec_ref(v_decls_3532_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* v_decls_3540_, lean_object* v_b_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lean_Meta_Closure_mkLambda(v_decls_3540_, v_b_3541_);
lean_dec_ref(v_b_3541_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(lean_object* v_decls_3543_, lean_object* v_xs_3544_, lean_object* v_x_3545_, lean_object* v_x_3546_){
_start:
{
lean_object* v_zero_3547_; uint8_t v_isZero_3548_; 
v_zero_3547_ = lean_unsigned_to_nat(0u);
v_isZero_3548_ = lean_nat_dec_eq(v_x_3545_, v_zero_3547_);
if (v_isZero_3548_ == 1)
{
lean_dec(v_x_3545_);
return v_x_3546_;
}
else
{
lean_object* v_one_3549_; lean_object* v_n_3550_; lean_object* v_decl_3551_; 
v_one_3549_ = lean_unsigned_to_nat(1u);
v_n_3550_ = lean_nat_sub(v_x_3545_, v_one_3549_);
lean_dec(v_x_3545_);
v_decl_3551_ = lean_array_fget_borrowed(v_decls_3543_, v_n_3550_);
if (lean_obj_tag(v_decl_3551_) == 0)
{
lean_object* v_userName_3552_; lean_object* v_type_3553_; uint8_t v_bi_3554_; lean_object* v_ty_3555_; lean_object* v___x_3556_; 
v_userName_3552_ = lean_ctor_get(v_decl_3551_, 2);
v_type_3553_ = lean_ctor_get(v_decl_3551_, 3);
v_bi_3554_ = lean_ctor_get_uint8(v_decl_3551_, sizeof(void*)*4);
v_ty_3555_ = lean_expr_abstract_range(v_type_3553_, v_n_3550_, v_xs_3544_);
lean_inc(v_userName_3552_);
v___x_3556_ = l_Lean_mkForall(v_userName_3552_, v_bi_3554_, v_ty_3555_, v_x_3546_);
v_x_3545_ = v_n_3550_;
v_x_3546_ = v___x_3556_;
goto _start;
}
else
{
lean_object* v_userName_3558_; lean_object* v_type_3559_; lean_object* v_value_3560_; uint8_t v_nondep_3561_; uint8_t v___x_3562_; 
v_userName_3558_ = lean_ctor_get(v_decl_3551_, 2);
v_type_3559_ = lean_ctor_get(v_decl_3551_, 3);
v_value_3560_ = lean_ctor_get(v_decl_3551_, 4);
v_nondep_3561_ = lean_ctor_get_uint8(v_decl_3551_, sizeof(void*)*5);
v___x_3562_ = lean_expr_has_loose_bvar(v_x_3546_, v_zero_3547_);
if (v___x_3562_ == 0)
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_expr_lower_loose_bvars(v_x_3546_, v_one_3549_, v_one_3549_);
lean_dec_ref(v_x_3546_);
v_x_3545_ = v_n_3550_;
v_x_3546_ = v___x_3563_;
goto _start;
}
else
{
lean_object* v_ty_3565_; lean_object* v_val_3566_; lean_object* v___x_3567_; 
v_ty_3565_ = lean_expr_abstract_range(v_type_3559_, v_n_3550_, v_xs_3544_);
v_val_3566_ = lean_expr_abstract_range(v_value_3560_, v_n_3550_, v_xs_3544_);
lean_inc(v_userName_3558_);
v___x_3567_ = l_Lean_Expr_letE___override(v_userName_3558_, v_ty_3565_, v_val_3566_, v_x_3546_, v_nondep_3561_);
v_x_3545_ = v_n_3550_;
v_x_3546_ = v___x_3567_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0___boxed(lean_object* v_decls_3569_, lean_object* v_xs_3570_, lean_object* v_x_3571_, lean_object* v_x_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_3569_, v_xs_3570_, v_x_3571_, v_x_3572_);
lean_dec_ref(v_xs_3570_);
lean_dec_ref(v_decls_3569_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(lean_object* v_decls_3574_, lean_object* v_xs_3575_, lean_object* v_x_3576_, lean_object* v_x_3577_){
_start:
{
lean_object* v_zero_3578_; uint8_t v_isZero_3579_; 
v_zero_3578_ = lean_unsigned_to_nat(0u);
v_isZero_3579_ = lean_nat_dec_eq(v_x_3576_, v_zero_3578_);
if (v_isZero_3579_ == 1)
{
return v_x_3577_;
}
else
{
lean_object* v_one_3580_; lean_object* v_n_3581_; lean_object* v_decl_3582_; 
v_one_3580_ = lean_unsigned_to_nat(1u);
v_n_3581_ = lean_nat_sub(v_x_3576_, v_one_3580_);
v_decl_3582_ = lean_array_fget_borrowed(v_decls_3574_, v_n_3581_);
if (lean_obj_tag(v_decl_3582_) == 0)
{
lean_object* v_userName_3583_; lean_object* v_type_3584_; uint8_t v_bi_3585_; lean_object* v_ty_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v_userName_3583_ = lean_ctor_get(v_decl_3582_, 2);
v_type_3584_ = lean_ctor_get(v_decl_3582_, 3);
v_bi_3585_ = lean_ctor_get_uint8(v_decl_3582_, sizeof(void*)*4);
v_ty_3586_ = lean_expr_abstract_range(v_type_3584_, v_n_3581_, v_xs_3575_);
lean_inc(v_userName_3583_);
v___x_3587_ = l_Lean_mkForall(v_userName_3583_, v_bi_3585_, v_ty_3586_, v_x_3577_);
v___x_3588_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_3574_, v_xs_3575_, v_n_3581_, v___x_3587_);
return v___x_3588_;
}
else
{
lean_object* v_userName_3589_; lean_object* v_type_3590_; lean_object* v_value_3591_; uint8_t v_nondep_3592_; uint8_t v___x_3593_; 
v_userName_3589_ = lean_ctor_get(v_decl_3582_, 2);
v_type_3590_ = lean_ctor_get(v_decl_3582_, 3);
v_value_3591_ = lean_ctor_get(v_decl_3582_, 4);
v_nondep_3592_ = lean_ctor_get_uint8(v_decl_3582_, sizeof(void*)*5);
v___x_3593_ = lean_expr_has_loose_bvar(v_x_3577_, v_zero_3578_);
if (v___x_3593_ == 0)
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = lean_expr_lower_loose_bvars(v_x_3577_, v_one_3580_, v_one_3580_);
lean_dec_ref(v_x_3577_);
v___x_3595_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_3574_, v_xs_3575_, v_n_3581_, v___x_3594_);
return v___x_3595_;
}
else
{
lean_object* v_ty_3596_; lean_object* v_val_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_ty_3596_ = lean_expr_abstract_range(v_type_3590_, v_n_3581_, v_xs_3575_);
v_val_3597_ = lean_expr_abstract_range(v_value_3591_, v_n_3581_, v_xs_3575_);
lean_inc(v_userName_3589_);
v___x_3598_ = l_Lean_Expr_letE___override(v_userName_3589_, v_ty_3596_, v_val_3597_, v_x_3577_, v_nondep_3592_);
v___x_3599_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_3574_, v_xs_3575_, v_n_3581_, v___x_3598_);
return v___x_3599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object* v_decls_3600_, lean_object* v_xs_3601_, lean_object* v_x_3602_, lean_object* v_x_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_3600_, v_xs_3601_, v_x_3602_, v_x_3603_);
lean_dec(v_x_3602_);
lean_dec_ref(v_xs_3601_);
lean_dec_ref(v_decls_3600_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* v_decls_3605_, lean_object* v_b_3606_){
_start:
{
size_t v_sz_3607_; size_t v___x_3608_; lean_object* v_xs_3609_; lean_object* v_b_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v_sz_3607_ = lean_array_size(v_decls_3605_);
v___x_3608_ = ((size_t)0ULL);
lean_inc_ref(v_decls_3605_);
v_xs_3609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_3607_, v___x_3608_, v_decls_3605_);
v_b_3610_ = lean_expr_abstract(v_b_3606_, v_xs_3609_);
v___x_3611_ = lean_array_get_size(v_decls_3605_);
v___x_3612_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_3605_, v_xs_3609_, v___x_3611_, v_b_3610_);
lean_dec_ref(v_xs_3609_);
lean_dec_ref(v_decls_3605_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* v_decls_3613_, lean_object* v_b_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_Meta_Closure_mkForall(v_decls_3613_, v_b_3614_);
lean_dec_ref(v_b_3614_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object* v_a_3616_, lean_object* v_zetaDeltaFVarIds_3617_, lean_object* v_a_x3f_3618_){
_start:
{
lean_object* v___x_3620_; lean_object* v_mctx_3621_; lean_object* v_cache_3622_; lean_object* v_postponed_3623_; lean_object* v_diag_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3634_; 
v___x_3620_ = lean_st_ref_take(v_a_3616_);
v_mctx_3621_ = lean_ctor_get(v___x_3620_, 0);
v_cache_3622_ = lean_ctor_get(v___x_3620_, 1);
v_postponed_3623_ = lean_ctor_get(v___x_3620_, 3);
v_diag_3624_ = lean_ctor_get(v___x_3620_, 4);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3634_ == 0)
{
lean_object* v_unused_3635_; 
v_unused_3635_ = lean_ctor_get(v___x_3620_, 2);
lean_dec(v_unused_3635_);
v___x_3626_ = v___x_3620_;
v_isShared_3627_ = v_isSharedCheck_3634_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_diag_3624_);
lean_inc(v_postponed_3623_);
lean_inc(v_cache_3622_);
lean_inc(v_mctx_3621_);
lean_dec(v___x_3620_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3634_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 2, v_zetaDeltaFVarIds_3617_);
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_mctx_3621_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_cache_3622_);
lean_ctor_set(v_reuseFailAlloc_3633_, 2, v_zetaDeltaFVarIds_3617_);
lean_ctor_set(v_reuseFailAlloc_3633_, 3, v_postponed_3623_);
lean_ctor_set(v_reuseFailAlloc_3633_, 4, v_diag_3624_);
v___x_3629_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3630_ = lean_st_ref_put(v_a_3616_, v___x_3629_);
v___x_3631_ = lean_box(0);
v___x_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
return v___x_3632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object* v_a_3636_, lean_object* v_zetaDeltaFVarIds_3637_, lean_object* v_a_x3f_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_3636_, v_zetaDeltaFVarIds_3637_, v_a_x3f_3638_);
lean_dec(v_a_x3f_3638_);
lean_dec(v_a_3636_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object* v_a_3641_, lean_object* v_cache_3642_, lean_object* v_a_x3f_3643_){
_start:
{
lean_object* v___x_3645_; lean_object* v_mctx_3646_; lean_object* v_zetaDeltaFVarIds_3647_; lean_object* v_postponed_3648_; lean_object* v_diag_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3659_; 
v___x_3645_ = lean_st_ref_take(v_a_3641_);
v_mctx_3646_ = lean_ctor_get(v___x_3645_, 0);
v_zetaDeltaFVarIds_3647_ = lean_ctor_get(v___x_3645_, 2);
v_postponed_3648_ = lean_ctor_get(v___x_3645_, 3);
v_diag_3649_ = lean_ctor_get(v___x_3645_, 4);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v___x_3645_, 1);
lean_dec(v_unused_3660_);
v___x_3651_ = v___x_3645_;
v_isShared_3652_ = v_isSharedCheck_3659_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_diag_3649_);
lean_inc(v_postponed_3648_);
lean_inc(v_zetaDeltaFVarIds_3647_);
lean_inc(v_mctx_3646_);
lean_dec(v___x_3645_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3659_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 1, v_cache_3642_);
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_mctx_3646_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_cache_3642_);
lean_ctor_set(v_reuseFailAlloc_3658_, 2, v_zetaDeltaFVarIds_3647_);
lean_ctor_set(v_reuseFailAlloc_3658_, 3, v_postponed_3648_);
lean_ctor_set(v_reuseFailAlloc_3658_, 4, v_diag_3649_);
v___x_3654_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = lean_st_ref_put(v_a_3641_, v___x_3654_);
v___x_3656_ = lean_box(0);
v___x_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
return v___x_3657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object* v_a_3661_, lean_object* v_cache_3662_, lean_object* v_a_x3f_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_3661_, v_cache_3662_, v_a_x3f_3663_);
lean_dec(v_a_x3f_3663_);
lean_dec(v_a_3661_);
return v_res_3665_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0(void){
_start:
{
lean_object* v___x_3666_; 
v___x_3666_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3666_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1(void){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
return v___x_3668_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2(void){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3669_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_3670_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
lean_ctor_set(v___x_3670_, 2, v___x_3669_);
lean_ctor_set(v___x_3670_, 3, v___x_3669_);
lean_ctor_set(v___x_3670_, 4, v___x_3669_);
lean_ctor_set(v___x_3670_, 5, v___x_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* v_type_3671_, lean_object* v_value_3672_, uint8_t v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v_mctx_3682_; lean_object* v_zetaDeltaFVarIds_3683_; lean_object* v_postponed_3684_; lean_object* v_diag_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3765_; 
v___x_3680_ = lean_st_ref_get(v_a_3676_);
v___x_3681_ = lean_st_ref_take(v_a_3676_);
v_mctx_3682_ = lean_ctor_get(v___x_3681_, 0);
v_zetaDeltaFVarIds_3683_ = lean_ctor_get(v___x_3681_, 2);
v_postponed_3684_ = lean_ctor_get(v___x_3681_, 3);
v_diag_3685_ = lean_ctor_get(v___x_3681_, 4);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3765_ == 0)
{
lean_object* v_unused_3766_; 
v_unused_3766_ = lean_ctor_get(v___x_3681_, 1);
lean_dec(v_unused_3766_);
v___x_3687_ = v___x_3681_;
v_isShared_3688_ = v_isSharedCheck_3765_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_diag_3685_);
lean_inc(v_postponed_3684_);
lean_inc(v_zetaDeltaFVarIds_3683_);
lean_inc(v_mctx_3682_);
lean_dec(v___x_3681_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3765_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3689_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 1, v___x_3689_);
v___x_3691_ = v___x_3687_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_mctx_3682_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3764_, 2, v_zetaDeltaFVarIds_3683_);
lean_ctor_set(v_reuseFailAlloc_3764_, 3, v_postponed_3684_);
lean_ctor_set(v_reuseFailAlloc_3764_, 4, v_diag_3685_);
v___x_3691_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v_mctx_3694_; lean_object* v_cache_3695_; lean_object* v_zetaDeltaFVarIds_3696_; lean_object* v_postponed_3697_; lean_object* v_diag_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3763_; 
v___x_3692_ = lean_st_ref_put(v_a_3676_, v___x_3691_);
v___x_3693_ = lean_st_ref_take(v_a_3676_);
v_mctx_3694_ = lean_ctor_get(v___x_3693_, 0);
v_cache_3695_ = lean_ctor_get(v___x_3693_, 1);
v_zetaDeltaFVarIds_3696_ = lean_ctor_get(v___x_3693_, 2);
v_postponed_3697_ = lean_ctor_get(v___x_3693_, 3);
v_diag_3698_ = lean_ctor_get(v___x_3693_, 4);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3700_ = v___x_3693_;
v_isShared_3701_ = v_isSharedCheck_3763_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_diag_3698_);
lean_inc(v_postponed_3697_);
lean_inc(v_zetaDeltaFVarIds_3696_);
lean_inc(v_cache_3695_);
lean_inc(v_mctx_3694_);
lean_dec(v___x_3693_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3763_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3702_; lean_object* v___x_3704_; 
v___x_3702_ = lean_box(1);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 2, v___x_3702_);
v___x_3704_ = v___x_3700_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_mctx_3694_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_cache_3695_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_postponed_3697_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v_diag_3698_);
v___x_3704_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3705_; lean_object* v_cache_3706_; lean_object* v_keyedConfig_3707_; lean_object* v_zetaDeltaSet_3708_; lean_object* v_lctx_3709_; lean_object* v_localInstances_3710_; lean_object* v_defEqCtx_x3f_3711_; lean_object* v_synthPendingDepth_3712_; lean_object* v_customCanUnfoldPredicate_x3f_3713_; uint8_t v_univApprox_3714_; uint8_t v_inTypeClassResolution_3715_; uint8_t v_cacheInferType_3716_; lean_object* v_a_3718_; lean_object* v_a_3730_; uint8_t v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3705_ = lean_st_ref_put(v_a_3676_, v___x_3704_);
v_cache_3706_ = lean_ctor_get(v___x_3680_, 1);
lean_inc_ref(v_cache_3706_);
lean_dec(v___x_3680_);
v_keyedConfig_3707_ = lean_ctor_get(v_a_3675_, 0);
v_zetaDeltaSet_3708_ = lean_ctor_get(v_a_3675_, 1);
v_lctx_3709_ = lean_ctor_get(v_a_3675_, 2);
v_localInstances_3710_ = lean_ctor_get(v_a_3675_, 3);
v_defEqCtx_x3f_3711_ = lean_ctor_get(v_a_3675_, 4);
v_synthPendingDepth_3712_ = lean_ctor_get(v_a_3675_, 5);
v_customCanUnfoldPredicate_x3f_3713_ = lean_ctor_get(v_a_3675_, 6);
v_univApprox_3714_ = lean_ctor_get_uint8(v_a_3675_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3715_ = lean_ctor_get_uint8(v_a_3675_, sizeof(void*)*7 + 2);
v_cacheInferType_3716_ = lean_ctor_get_uint8(v_a_3675_, sizeof(void*)*7 + 3);
v___x_3733_ = 1;
lean_inc(v_customCanUnfoldPredicate_x3f_3713_);
lean_inc(v_synthPendingDepth_3712_);
lean_inc(v_defEqCtx_x3f_3711_);
lean_inc_ref(v_localInstances_3710_);
lean_inc_ref(v_lctx_3709_);
lean_inc(v_zetaDeltaSet_3708_);
lean_inc_ref(v_keyedConfig_3707_);
v___x_3734_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3734_, 0, v_keyedConfig_3707_);
lean_ctor_set(v___x_3734_, 1, v_zetaDeltaSet_3708_);
lean_ctor_set(v___x_3734_, 2, v_lctx_3709_);
lean_ctor_set(v___x_3734_, 3, v_localInstances_3710_);
lean_ctor_set(v___x_3734_, 4, v_defEqCtx_x3f_3711_);
lean_ctor_set(v___x_3734_, 5, v_synthPendingDepth_3712_);
lean_ctor_set(v___x_3734_, 6, v_customCanUnfoldPredicate_x3f_3713_);
lean_ctor_set_uint8(v___x_3734_, sizeof(void*)*7, v___x_3733_);
lean_ctor_set_uint8(v___x_3734_, sizeof(void*)*7 + 1, v_univApprox_3714_);
lean_ctor_set_uint8(v___x_3734_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3715_);
lean_ctor_set_uint8(v___x_3734_, sizeof(void*)*7 + 3, v_cacheInferType_3716_);
v___x_3735_ = l_Lean_Meta_Closure_collectExpr(v_type_3671_, v_a_3673_, v_a_3674_, v___x_3734_, v_a_3676_, v_a_3677_, v_a_3678_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3737_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
v___x_3737_ = l_Lean_Meta_Closure_collectExpr(v_value_3672_, v_a_3673_, v_a_3674_, v___x_3734_, v_a_3676_, v_a_3677_, v_a_3678_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3739_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v___x_3737_, 1);
v___x_3739_ = l_Lean_Meta_Closure_process(v_a_3673_, v_a_3674_, v___x_3734_, v_a_3676_, v_a_3677_, v_a_3678_);
lean_dec_ref_known(v___x_3734_, 7);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3757_; 
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3757_ == 0)
{
lean_object* v_unused_3758_; 
v_unused_3758_ = lean_ctor_get(v___x_3739_, 0);
lean_dec(v_unused_3758_);
v___x_3741_ = v___x_3739_;
v_isShared_3742_ = v_isSharedCheck_3757_;
goto v_resetjp_3740_;
}
else
{
lean_dec(v___x_3739_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3757_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3743_; lean_object* v___x_3745_; 
v___x_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3743_, 0, v_a_3736_);
lean_ctor_set(v___x_3743_, 1, v_a_3738_);
lean_inc_ref(v___x_3743_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set_tag(v___x_3741_, 1);
lean_ctor_set(v___x_3741_, 0, v___x_3743_);
v___x_3745_ = v___x_3741_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
v___x_3746_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_3676_, v_zetaDeltaFVarIds_3696_, v___x_3745_);
lean_dec_ref(v___x_3746_);
v___x_3747_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_3676_, v_cache_3706_, v___x_3745_);
lean_dec_ref(v___x_3745_);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3754_ == 0)
{
lean_object* v_unused_3755_; 
v_unused_3755_ = lean_ctor_get(v___x_3747_, 0);
lean_dec(v_unused_3755_);
v___x_3749_ = v___x_3747_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_dec(v___x_3747_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v___x_3743_);
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3743_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
else
{
lean_object* v_a_3759_; 
lean_dec(v_a_3738_);
lean_dec(v_a_3736_);
v_a_3759_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3759_);
lean_dec_ref_known(v___x_3739_, 1);
v_a_3730_ = v_a_3759_;
goto v___jp_3729_;
}
}
else
{
lean_object* v_a_3760_; 
lean_dec(v_a_3736_);
lean_dec_ref_known(v___x_3734_, 7);
v_a_3760_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3737_, 1);
v_a_3730_ = v_a_3760_;
goto v___jp_3729_;
}
}
else
{
lean_object* v_a_3761_; 
lean_dec_ref_known(v___x_3734_, 7);
lean_dec_ref(v_value_3672_);
v_a_3761_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v___x_3735_, 1);
v_a_3730_ = v_a_3761_;
goto v___jp_3729_;
}
v___jp_3717_:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
v___x_3719_ = lean_box(0);
v___x_3720_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_3676_, v_cache_3706_, v___x_3719_);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3727_ == 0)
{
lean_object* v_unused_3728_; 
v_unused_3728_ = lean_ctor_get(v___x_3720_, 0);
lean_dec(v_unused_3728_);
v___x_3722_ = v___x_3720_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_dec(v___x_3720_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
lean_ctor_set_tag(v___x_3722_, 1);
lean_ctor_set(v___x_3722_, 0, v_a_3718_);
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3718_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
v___jp_3729_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = lean_box(0);
v___x_3732_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_3676_, v_zetaDeltaFVarIds_3696_, v___x_3731_);
lean_dec_ref(v___x_3732_);
v_a_3718_ = v_a_3730_;
goto v___jp_3717_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* v_type_3767_, lean_object* v_value_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_){
_start:
{
uint8_t v_a_boxed_3776_; lean_object* v_res_3777_; 
v_a_boxed_3776_ = lean_unbox(v_a_3769_);
v_res_3777_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_3767_, v_value_3768_, v_a_boxed_3776_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
return v_res_3777_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_instMonadEIO(lean_box(0));
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object* v_msg_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v_toApplicative_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3829_; 
v___x_3786_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__0);
v___x_3787_ = l_StateRefT_x27_instMonad___redArg(v___x_3786_);
v_toApplicative_3788_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3829_ == 0)
{
lean_object* v_unused_3830_; 
v_unused_3830_ = lean_ctor_get(v___x_3787_, 1);
lean_dec(v_unused_3830_);
v___x_3790_ = v___x_3787_;
v_isShared_3791_ = v_isSharedCheck_3829_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_toApplicative_3788_);
lean_dec(v___x_3787_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3829_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v_toFunctor_3792_; lean_object* v_toSeq_3793_; lean_object* v_toSeqLeft_3794_; lean_object* v_toSeqRight_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3827_; 
v_toFunctor_3792_ = lean_ctor_get(v_toApplicative_3788_, 0);
v_toSeq_3793_ = lean_ctor_get(v_toApplicative_3788_, 2);
v_toSeqLeft_3794_ = lean_ctor_get(v_toApplicative_3788_, 3);
v_toSeqRight_3795_ = lean_ctor_get(v_toApplicative_3788_, 4);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_toApplicative_3788_);
if (v_isSharedCheck_3827_ == 0)
{
lean_object* v_unused_3828_; 
v_unused_3828_ = lean_ctor_get(v_toApplicative_3788_, 1);
lean_dec(v_unused_3828_);
v___x_3797_ = v_toApplicative_3788_;
v_isShared_3798_ = v_isSharedCheck_3827_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_toSeqRight_3795_);
lean_inc(v_toSeqLeft_3794_);
lean_inc(v_toSeq_3793_);
lean_inc(v_toFunctor_3792_);
lean_dec(v_toApplicative_3788_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3827_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___f_3799_; lean_object* v___f_3800_; lean_object* v___f_3801_; lean_object* v___f_3802_; lean_object* v___x_3803_; lean_object* v___f_3804_; lean_object* v___f_3805_; lean_object* v___f_3806_; lean_object* v___x_3808_; 
v___f_3799_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__1));
v___f_3800_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___closed__2));
lean_inc_ref(v_toFunctor_3792_);
v___f_3801_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3801_, 0, v_toFunctor_3792_);
v___f_3802_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3802_, 0, v_toFunctor_3792_);
v___x_3803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___f_3801_);
lean_ctor_set(v___x_3803_, 1, v___f_3802_);
v___f_3804_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3804_, 0, v_toSeqRight_3795_);
v___f_3805_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3805_, 0, v_toSeqLeft_3794_);
v___f_3806_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3806_, 0, v_toSeq_3793_);
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 4, v___f_3804_);
lean_ctor_set(v___x_3797_, 3, v___f_3805_);
lean_ctor_set(v___x_3797_, 2, v___f_3806_);
lean_ctor_set(v___x_3797_, 1, v___f_3799_);
lean_ctor_set(v___x_3797_, 0, v___x_3803_);
v___x_3808_ = v___x_3797_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v___f_3799_);
lean_ctor_set(v_reuseFailAlloc_3826_, 2, v___f_3806_);
lean_ctor_set(v_reuseFailAlloc_3826_, 3, v___f_3805_);
lean_ctor_set(v_reuseFailAlloc_3826_, 4, v___f_3804_);
v___x_3808_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
lean_object* v___x_3810_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 1, v___f_3800_);
lean_ctor_set(v___x_3790_, 0, v___x_3808_);
v___x_3810_ = v___x_3790_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v___f_3800_);
v___x_3810_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
lean_object* v___f_3811_; lean_object* v___f_3812_; lean_object* v___f_3813_; lean_object* v___f_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_20949__overap_3823_; lean_object* v___x_3824_; 
lean_inc_ref_n(v___x_3810_, 6);
v___f_3811_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3811_, 0, v___x_3810_);
v___f_3812_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3812_, 0, v___x_3810_);
v___f_3813_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_3813_, 0, v___x_3810_);
v___f_3814_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_3814_, 0, v___x_3810_);
v___x_3815_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_3815_, 0, lean_box(0));
lean_closure_set(v___x_3815_, 1, lean_box(0));
lean_closure_set(v___x_3815_, 2, v___x_3810_);
v___x_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
lean_ctor_set(v___x_3816_, 1, v___f_3811_);
v___x_3817_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_3817_, 0, lean_box(0));
lean_closure_set(v___x_3817_, 1, lean_box(0));
lean_closure_set(v___x_3817_, 2, v___x_3810_);
v___x_3818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
lean_ctor_set(v___x_3818_, 2, v___f_3812_);
lean_ctor_set(v___x_3818_, 3, v___f_3813_);
lean_ctor_set(v___x_3818_, 4, v___f_3814_);
v___x_3819_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_3819_, 0, lean_box(0));
lean_closure_set(v___x_3819_, 1, lean_box(0));
lean_closure_set(v___x_3819_, 2, v___x_3810_);
v___x_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3818_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = lean_box(0);
v___x_3822_ = l_instInhabitedOfMonad___redArg(v___x_3820_, v___x_3821_);
v___x_20949__overap_3823_ = lean_panic_fn_borrowed(v___x_3822_, v_msg_3781_);
lean_dec(v___x_3822_);
lean_inc(v___y_3784_);
lean_inc_ref(v___y_3783_);
v___x_3824_ = lean_apply_4(v___x_20949__overap_3823_, v___y_3782_, v___y_3783_, v___y_3784_, lean_box(0));
return v___x_3824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object* v_msg_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v_msg_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
return v_res_3836_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3837_; 
v___x_3837_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3837_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__1(void){
_start:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3838_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__0);
v___x_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3838_);
return v___x_3839_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__2(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3840_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__1);
v___x_3841_ = lean_unsigned_to_nat(0u);
v___x_3842_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3841_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
lean_ctor_set(v___x_3842_, 2, v___x_3841_);
lean_ctor_set(v___x_3842_, 3, v___x_3841_);
lean_ctor_set(v___x_3842_, 4, v___x_3840_);
lean_ctor_set(v___x_3842_, 5, v___x_3840_);
lean_ctor_set(v___x_3842_, 6, v___x_3840_);
lean_ctor_set(v___x_3842_, 7, v___x_3840_);
lean_ctor_set(v___x_3842_, 8, v___x_3840_);
lean_ctor_set(v___x_3842_, 9, v___x_3840_);
lean_ctor_set(v___x_3842_, 10, v___x_3840_);
return v___x_3842_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__3(void){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3843_ = lean_unsigned_to_nat(32u);
v___x_3844_ = lean_mk_empty_array_with_capacity(v___x_3843_);
v___x_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
return v___x_3845_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__4(void){
_start:
{
size_t v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3846_ = ((size_t)5ULL);
v___x_3847_ = lean_unsigned_to_nat(0u);
v___x_3848_ = lean_unsigned_to_nat(32u);
v___x_3849_ = lean_mk_empty_array_with_capacity(v___x_3848_);
v___x_3850_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__3);
v___x_3851_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
lean_ctor_set(v___x_3851_, 1, v___x_3849_);
lean_ctor_set(v___x_3851_, 2, v___x_3847_);
lean_ctor_set(v___x_3851_, 3, v___x_3847_);
lean_ctor_set_usize(v___x_3851_, 4, v___x_3846_);
return v___x_3851_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__5(void){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3852_ = lean_box(1);
v___x_3853_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__4);
v___x_3854_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__1);
v___x_3855_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
lean_ctor_set(v___x_3855_, 1, v___x_3853_);
lean_ctor_set(v___x_3855_, 2, v___x_3852_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12(lean_object* v_msgData_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v___x_3860_; lean_object* v_env_3861_; lean_object* v_options_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3860_ = lean_st_ref_get(v___y_3858_);
v_env_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc_ref(v_env_3861_);
lean_dec(v___x_3860_);
v_options_3862_ = lean_ctor_get(v___y_3857_, 2);
v___x_3863_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__2);
v___x_3864_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___closed__5);
lean_inc_ref(v_options_3862_);
v___x_3865_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3865_, 0, v_env_3861_);
lean_ctor_set(v___x_3865_, 1, v___x_3863_);
lean_ctor_set(v___x_3865_, 2, v___x_3864_);
lean_ctor_set(v___x_3865_, 3, v_options_3862_);
v___x_3866_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3865_);
lean_ctor_set(v___x_3866_, 1, v_msgData_3856_);
v___x_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12___boxed(lean_object* v_msgData_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12(v_msgData_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___redArg(lean_object* v_msg_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_ref_3877_; lean_object* v___x_3878_; lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3887_; 
v_ref_3877_ = lean_ctor_get(v___y_3874_, 5);
v___x_3878_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12(v_msg_3873_, v___y_3874_, v___y_3875_);
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3881_ = v___x_3878_;
v_isShared_3882_ = v_isSharedCheck_3887_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3887_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; lean_object* v___x_3885_; 
lean_inc(v_ref_3877_);
v___x_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3883_, 0, v_ref_3877_);
lean_ctor_set(v___x_3883_, 1, v_a_3879_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set_tag(v___x_3881_, 1);
lean_ctor_set(v___x_3881_, 0, v___x_3883_);
v___x_3885_ = v___x_3881_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3883_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___redArg___boxed(lean_object* v_msg_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___redArg(v_msg_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
return v_res_3892_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__0(void){
_start:
{
lean_object* v___x_3893_; double v___x_3894_; 
v___x_3893_ = lean_unsigned_to_nat(0u);
v___x_3894_ = lean_float_of_nat(v___x_3893_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7(lean_object* v_cls_3898_, lean_object* v_msg_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_ref_3904_; lean_object* v___x_3905_; lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3951_; 
v_ref_3904_ = lean_ctor_get(v___y_3901_, 5);
v___x_3905_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12(v_msg_3899_, v___y_3901_, v___y_3902_);
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3908_ = v___x_3905_;
v_isShared_3909_ = v_isSharedCheck_3951_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3905_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3951_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3910_; lean_object* v_traceState_3911_; lean_object* v_env_3912_; lean_object* v_nextMacroScope_3913_; lean_object* v_ngen_3914_; lean_object* v_auxDeclNGen_3915_; lean_object* v_cache_3916_; lean_object* v_messages_3917_; lean_object* v_infoState_3918_; lean_object* v_snapshotTasks_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3950_; 
v___x_3910_ = lean_st_ref_take(v___y_3902_);
v_traceState_3911_ = lean_ctor_get(v___x_3910_, 4);
v_env_3912_ = lean_ctor_get(v___x_3910_, 0);
v_nextMacroScope_3913_ = lean_ctor_get(v___x_3910_, 1);
v_ngen_3914_ = lean_ctor_get(v___x_3910_, 2);
v_auxDeclNGen_3915_ = lean_ctor_get(v___x_3910_, 3);
v_cache_3916_ = lean_ctor_get(v___x_3910_, 5);
v_messages_3917_ = lean_ctor_get(v___x_3910_, 6);
v_infoState_3918_ = lean_ctor_get(v___x_3910_, 7);
v_snapshotTasks_3919_ = lean_ctor_get(v___x_3910_, 8);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3921_ = v___x_3910_;
v_isShared_3922_ = v_isSharedCheck_3950_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_snapshotTasks_3919_);
lean_inc(v_infoState_3918_);
lean_inc(v_messages_3917_);
lean_inc(v_cache_3916_);
lean_inc(v_traceState_3911_);
lean_inc(v_auxDeclNGen_3915_);
lean_inc(v_ngen_3914_);
lean_inc(v_nextMacroScope_3913_);
lean_inc(v_env_3912_);
lean_dec(v___x_3910_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3950_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
uint64_t v_tid_3923_; lean_object* v_traces_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3949_; 
v_tid_3923_ = lean_ctor_get_uint64(v_traceState_3911_, sizeof(void*)*1);
v_traces_3924_ = lean_ctor_get(v_traceState_3911_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v_traceState_3911_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3926_ = v_traceState_3911_;
v_isShared_3927_ = v_isSharedCheck_3949_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_traces_3924_);
lean_dec(v_traceState_3911_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3949_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3928_; double v___x_3929_; uint8_t v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3938_; 
v___x_3928_ = lean_box(0);
v___x_3929_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__0);
v___x_3930_ = 0;
v___x_3931_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__1));
v___x_3932_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3932_, 0, v_cls_3898_);
lean_ctor_set(v___x_3932_, 1, v___x_3928_);
lean_ctor_set(v___x_3932_, 2, v___x_3931_);
lean_ctor_set_float(v___x_3932_, sizeof(void*)*3, v___x_3929_);
lean_ctor_set_float(v___x_3932_, sizeof(void*)*3 + 8, v___x_3929_);
lean_ctor_set_uint8(v___x_3932_, sizeof(void*)*3 + 16, v___x_3930_);
v___x_3933_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__2));
v___x_3934_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3932_);
lean_ctor_set(v___x_3934_, 1, v_a_3906_);
lean_ctor_set(v___x_3934_, 2, v___x_3933_);
lean_inc(v_ref_3904_);
v___x_3935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3935_, 0, v_ref_3904_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___x_3936_ = l_Lean_PersistentArray_push___redArg(v_traces_3924_, v___x_3935_);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 0, v___x_3936_);
v___x_3938_ = v___x_3926_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3936_);
lean_ctor_set_uint64(v_reuseFailAlloc_3948_, sizeof(void*)*1, v_tid_3923_);
v___x_3938_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3940_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v___x_3938_);
v___x_3940_ = v___x_3921_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_env_3912_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v_nextMacroScope_3913_);
lean_ctor_set(v_reuseFailAlloc_3947_, 2, v_ngen_3914_);
lean_ctor_set(v_reuseFailAlloc_3947_, 3, v_auxDeclNGen_3915_);
lean_ctor_set(v_reuseFailAlloc_3947_, 4, v___x_3938_);
lean_ctor_set(v_reuseFailAlloc_3947_, 5, v_cache_3916_);
lean_ctor_set(v_reuseFailAlloc_3947_, 6, v_messages_3917_);
lean_ctor_set(v_reuseFailAlloc_3947_, 7, v_infoState_3918_);
lean_ctor_set(v_reuseFailAlloc_3947_, 8, v_snapshotTasks_3919_);
v___x_3940_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3941_ = lean_st_ref_put(v___y_3902_, v___x_3940_);
v___x_3942_ = lean_box(0);
v___x_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
lean_ctor_set(v___x_3943_, 1, v___y_3900_);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3943_);
v___x_3945_ = v___x_3908_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3943_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___boxed(lean_object* v_cls_3952_, lean_object* v_msg_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7(v_cls_3952_, v_msg_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(lean_object* v_m_3959_, lean_object* v_query_3960_, lean_object* v_x_3961_, lean_object* v_x_3962_, lean_object* v_x_3963_){
_start:
{
lean_object* v_zero_3964_; uint8_t v_isZero_3965_; 
v_zero_3964_ = lean_unsigned_to_nat(0u);
v_isZero_3965_ = lean_nat_dec_eq(v_x_3962_, v_zero_3964_);
if (v_isZero_3965_ == 1)
{
lean_dec(v_x_3963_);
lean_dec(v_x_3962_);
if (lean_obj_tag(v_x_3961_) == 0)
{
lean_object* v___x_3966_; 
v___x_3966_ = lean_box(2);
return v___x_3966_;
}
else
{
lean_object* v_val_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
v_val_3967_ = lean_ctor_get(v_x_3961_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v_x_3961_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v_x_3961_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_val_3967_);
lean_dec(v_x_3961_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_val_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
else
{
lean_object* v_keyArray_3975_; lean_object* v_valueArray_3976_; lean_object* v___x_3977_; uint8_t v_isSome_3978_; 
v_keyArray_3975_ = lean_ctor_get(v_m_3959_, 1);
v_valueArray_3976_ = lean_ctor_get(v_m_3959_, 2);
v___x_3977_ = lean_array_fget_borrowed(v_keyArray_3975_, v_x_3963_);
v_isSome_3978_ = lean_noption_is_some(v___x_3977_);
if (v_isSome_3978_ == 0)
{
lean_dec(v_x_3962_);
if (lean_obj_tag(v_x_3961_) == 0)
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3979_, 0, v_x_3963_);
return v___x_3979_;
}
else
{
lean_object* v_val_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec(v_x_3963_);
v_val_3980_ = lean_ctor_get(v_x_3961_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_x_3961_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v_x_3961_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_val_3980_);
lean_dec(v_x_3961_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_val_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_object* v_one_3988_; lean_object* v_n_3989_; lean_object* v___y_3991_; 
v_one_3988_ = lean_unsigned_to_nat(1u);
v_n_3989_ = lean_nat_sub(v_x_3962_, v_one_3988_);
lean_dec(v_x_3962_);
if (v_isSome_3978_ == 0)
{
goto v___jp_3997_;
}
else
{
lean_object* v___x_3999_; uint8_t v_isSome_4000_; 
v___x_3999_ = lean_array_fget_borrowed(v_valueArray_3976_, v_x_3963_);
v_isSome_4000_ = lean_noption_is_some(v___x_3999_);
if (v_isSome_4000_ == 0)
{
goto v___jp_3997_;
}
else
{
lean_object* v_val_4001_; uint8_t v___x_4002_; 
lean_inc(v___x_3977_);
v_val_4001_ = lean_noption_get(v___x_3977_);
v___x_4002_ = l_Lean_instBEqFVarId_beq(v_val_4001_, v_query_3960_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; 
lean_dec(v_val_4001_);
v___x_4003_ = lean_array_get_size(v_keyArray_3975_);
v___x_4004_ = lean_nat_add(v_x_3963_, v_one_3988_);
lean_dec(v_x_3963_);
v___x_4005_ = lean_nat_dec_lt(v___x_4004_, v___x_4003_);
if (v___x_4005_ == 0)
{
lean_dec(v___x_4004_);
v_x_3962_ = v_n_3989_;
v_x_3963_ = v_zero_3964_;
goto _start;
}
else
{
v_x_3962_ = v_n_3989_;
v_x_3963_ = v___x_4004_;
goto _start;
}
}
else
{
lean_object* v_val_4008_; lean_object* v___x_4009_; 
lean_dec(v_n_3989_);
lean_dec(v_x_3961_);
lean_inc(v___x_3999_);
v_val_4008_ = lean_noption_get(v___x_3999_);
v___x_4009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4009_, 0, v_x_3963_);
lean_ctor_set(v___x_4009_, 1, v_val_4001_);
lean_ctor_set(v___x_4009_, 2, v_val_4008_);
return v___x_4009_;
}
}
}
v___jp_3990_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v___x_3992_ = lean_array_get_size(v_keyArray_3975_);
v___x_3993_ = lean_nat_add(v_x_3963_, v_one_3988_);
lean_dec(v_x_3963_);
v___x_3994_ = lean_nat_dec_lt(v___x_3993_, v___x_3992_);
if (v___x_3994_ == 0)
{
lean_dec(v___x_3993_);
v_x_3961_ = v___y_3991_;
v_x_3962_ = v_n_3989_;
v_x_3963_ = v_zero_3964_;
goto _start;
}
else
{
v_x_3961_ = v___y_3991_;
v_x_3962_ = v_n_3989_;
v_x_3963_ = v___x_3993_;
goto _start;
}
}
v___jp_3997_:
{
if (lean_obj_tag(v_x_3961_) == 0)
{
lean_object* v___x_3998_; 
lean_inc(v_x_3963_);
v___x_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3998_, 0, v_x_3963_);
v___y_3991_ = v___x_3998_;
goto v___jp_3990_;
}
else
{
v___y_3991_ = v_x_3961_;
goto v___jp_3990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg___boxed(lean_object* v_m_4010_, lean_object* v_query_4011_, lean_object* v_x_4012_, lean_object* v_x_4013_, lean_object* v_x_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_4010_, v_query_4011_, v_x_4012_, v_x_4013_, v_x_4014_);
lean_dec(v_query_4011_);
lean_dec_ref(v_m_4010_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(lean_object* v_m_4016_, lean_object* v_query_4017_){
_start:
{
lean_object* v_keyArray_4018_; lean_object* v___x_4019_; uint64_t v___x_4020_; uint64_t v___x_4021_; uint64_t v___x_4022_; uint64_t v_fold_4023_; uint64_t v___x_4024_; uint64_t v___x_4025_; uint64_t v___x_4026_; size_t v___x_4027_; size_t v___x_4028_; size_t v___x_4029_; size_t v___x_4030_; size_t v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v_keyArray_4018_ = lean_ctor_get(v_m_4016_, 1);
v___x_4019_ = lean_array_get_size(v_keyArray_4018_);
v___x_4020_ = l_Lean_instHashableFVarId_hash(v_query_4017_);
v___x_4021_ = 32ULL;
v___x_4022_ = lean_uint64_shift_right(v___x_4020_, v___x_4021_);
v_fold_4023_ = lean_uint64_xor(v___x_4020_, v___x_4022_);
v___x_4024_ = 16ULL;
v___x_4025_ = lean_uint64_shift_right(v_fold_4023_, v___x_4024_);
v___x_4026_ = lean_uint64_xor(v_fold_4023_, v___x_4025_);
v___x_4027_ = lean_uint64_to_usize(v___x_4026_);
v___x_4028_ = lean_usize_of_nat(v___x_4019_);
v___x_4029_ = ((size_t)1ULL);
v___x_4030_ = lean_usize_sub(v___x_4028_, v___x_4029_);
v___x_4031_ = lean_usize_land(v___x_4027_, v___x_4030_);
v___x_4032_ = lean_usize_to_nat(v___x_4031_);
v___x_4033_ = lean_box(0);
v___x_4034_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_4016_, v_query_4017_, v___x_4033_, v___x_4019_, v___x_4032_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg___boxed(lean_object* v_m_4035_, lean_object* v_query_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v_m_4035_, v_query_4036_);
lean_dec(v_query_4036_);
lean_dec_ref(v_m_4035_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object* v_m_4038_, lean_object* v_query_4039_){
_start:
{
lean_object* v___x_4040_; 
v___x_4040_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v_m_4038_, v_query_4039_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_index_4041_; lean_object* v_key_4042_; lean_object* v_value_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
v_index_4041_ = lean_ctor_get(v___x_4040_, 0);
v_key_4042_ = lean_ctor_get(v___x_4040_, 1);
v_value_4043_ = lean_ctor_get(v___x_4040_, 2);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4040_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_value_4043_);
lean_inc(v_key_4042_);
lean_inc(v_index_4041_);
lean_dec(v___x_4040_);
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
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_index_4041_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_key_4042_);
lean_ctor_set(v_reuseFailAlloc_4049_, 2, v_value_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
else
{
lean_object* v___x_4051_; 
lean_dec(v___x_4040_);
v___x_4051_ = lean_box(1);
return v___x_4051_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object* v_m_4052_, lean_object* v_query_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_m_4052_, v_query_4053_);
lean_dec(v_query_4053_);
lean_dec_ref(v_m_4052_);
return v_res_4054_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object* v_m_4055_, lean_object* v_a_4056_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_m_4055_, v_a_4056_);
if (lean_obj_tag(v___x_4057_) == 0)
{
uint8_t v___x_4058_; 
lean_dec_ref_known(v___x_4057_, 3);
v___x_4058_ = 1;
return v___x_4058_;
}
else
{
uint8_t v___x_4059_; 
v___x_4059_ = 0;
return v___x_4059_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object* v_m_4060_, lean_object* v_a_4061_){
_start:
{
uint8_t v_res_4062_; lean_object* v_r_4063_; 
v_res_4062_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_4060_, v_a_4061_);
lean_dec(v_a_4061_);
lean_dec_ref(v_m_4060_);
v_r_4063_ = lean_box(v_res_4062_);
return v_r_4063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__7___redArg(lean_object* v_m_4064_, lean_object* v_query_4065_, lean_object* v_x_4066_, lean_object* v_x_4067_, lean_object* v_x_4068_){
_start:
{
lean_object* v_zero_4069_; uint8_t v_isZero_4070_; 
v_zero_4069_ = lean_unsigned_to_nat(0u);
v_isZero_4070_ = lean_nat_dec_eq(v_x_4067_, v_zero_4069_);
if (v_isZero_4070_ == 1)
{
lean_dec(v_x_4068_);
lean_dec(v_x_4067_);
if (lean_obj_tag(v_x_4066_) == 0)
{
lean_object* v___x_4071_; 
v___x_4071_ = lean_box(2);
return v___x_4071_;
}
else
{
lean_object* v_val_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4079_; 
v_val_4072_ = lean_ctor_get(v_x_4066_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v_x_4066_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4074_ = v_x_4066_;
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_val_4072_);
lean_dec(v_x_4066_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4075_ == 0)
{
v___x_4077_ = v___x_4074_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_val_4072_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
}
else
{
lean_object* v_keyArray_4080_; lean_object* v_valueArray_4081_; lean_object* v___x_4082_; uint8_t v_isSome_4083_; 
v_keyArray_4080_ = lean_ctor_get(v_m_4064_, 1);
v_valueArray_4081_ = lean_ctor_get(v_m_4064_, 2);
v___x_4082_ = lean_array_fget_borrowed(v_keyArray_4080_, v_x_4068_);
v_isSome_4083_ = lean_noption_is_some(v___x_4082_);
if (v_isSome_4083_ == 0)
{
lean_dec(v_x_4067_);
if (lean_obj_tag(v_x_4066_) == 0)
{
lean_object* v___x_4084_; 
v___x_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4084_, 0, v_x_4068_);
return v___x_4084_;
}
else
{
lean_object* v_val_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec(v_x_4068_);
v_val_4085_ = lean_ctor_get(v_x_4066_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_x_4066_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v_x_4066_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_val_4085_);
lean_dec(v_x_4066_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_val_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
else
{
lean_object* v_one_4093_; lean_object* v_n_4094_; lean_object* v___y_4096_; 
v_one_4093_ = lean_unsigned_to_nat(1u);
v_n_4094_ = lean_nat_sub(v_x_4067_, v_one_4093_);
lean_dec(v_x_4067_);
if (v_isSome_4083_ == 0)
{
goto v___jp_4102_;
}
else
{
lean_object* v___x_4104_; uint8_t v_isSome_4105_; 
v___x_4104_ = lean_array_fget_borrowed(v_valueArray_4081_, v_x_4068_);
v_isSome_4105_ = lean_noption_is_some(v___x_4104_);
if (v_isSome_4105_ == 0)
{
goto v___jp_4102_;
}
else
{
lean_object* v_val_4106_; uint8_t v___x_4107_; 
lean_inc(v___x_4082_);
v_val_4106_ = lean_noption_get(v___x_4082_);
v___x_4107_ = lean_expr_eqv(v_val_4106_, v_query_4065_);
if (v___x_4107_ == 0)
{
lean_object* v___x_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; 
lean_dec(v_val_4106_);
v___x_4108_ = lean_array_get_size(v_keyArray_4080_);
v___x_4109_ = lean_nat_add(v_x_4068_, v_one_4093_);
lean_dec(v_x_4068_);
v___x_4110_ = lean_nat_dec_lt(v___x_4109_, v___x_4108_);
if (v___x_4110_ == 0)
{
lean_dec(v___x_4109_);
v_x_4067_ = v_n_4094_;
v_x_4068_ = v_zero_4069_;
goto _start;
}
else
{
v_x_4067_ = v_n_4094_;
v_x_4068_ = v___x_4109_;
goto _start;
}
}
else
{
lean_object* v_val_4113_; lean_object* v___x_4114_; 
lean_dec(v_n_4094_);
lean_dec(v_x_4066_);
lean_inc(v___x_4104_);
v_val_4113_ = lean_noption_get(v___x_4104_);
v___x_4114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4114_, 0, v_x_4068_);
lean_ctor_set(v___x_4114_, 1, v_val_4106_);
lean_ctor_set(v___x_4114_, 2, v_val_4113_);
return v___x_4114_;
}
}
}
v___jp_4095_:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
v___x_4097_ = lean_array_get_size(v_keyArray_4080_);
v___x_4098_ = lean_nat_add(v_x_4068_, v_one_4093_);
lean_dec(v_x_4068_);
v___x_4099_ = lean_nat_dec_lt(v___x_4098_, v___x_4097_);
if (v___x_4099_ == 0)
{
lean_dec(v___x_4098_);
v_x_4066_ = v___y_4096_;
v_x_4067_ = v_n_4094_;
v_x_4068_ = v_zero_4069_;
goto _start;
}
else
{
v_x_4066_ = v___y_4096_;
v_x_4067_ = v_n_4094_;
v_x_4068_ = v___x_4098_;
goto _start;
}
}
v___jp_4102_:
{
if (lean_obj_tag(v_x_4066_) == 0)
{
lean_object* v___x_4103_; 
lean_inc(v_x_4068_);
v___x_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4103_, 0, v_x_4068_);
v___y_4096_ = v___x_4103_;
goto v___jp_4095_;
}
else
{
v___y_4096_ = v_x_4066_;
goto v___jp_4095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_m_4115_, lean_object* v_query_4116_, lean_object* v_x_4117_, lean_object* v_x_4118_, lean_object* v_x_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__7___redArg(v_m_4115_, v_query_4116_, v_x_4117_, v_x_4118_, v_x_4119_);
lean_dec_ref(v_query_4116_);
lean_dec_ref(v_m_4115_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(lean_object* v_m_4121_, lean_object* v_query_4122_){
_start:
{
lean_object* v_keyArray_4123_; lean_object* v___x_4124_; uint64_t v___x_4125_; uint64_t v___x_4126_; uint64_t v___x_4127_; uint64_t v_fold_4128_; uint64_t v___x_4129_; uint64_t v___x_4130_; uint64_t v___x_4131_; size_t v___x_4132_; size_t v___x_4133_; size_t v___x_4134_; size_t v___x_4135_; size_t v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v_keyArray_4123_ = lean_ctor_get(v_m_4121_, 1);
v___x_4124_ = lean_array_get_size(v_keyArray_4123_);
v___x_4125_ = l_Lean_Expr_hash(v_query_4122_);
v___x_4126_ = 32ULL;
v___x_4127_ = lean_uint64_shift_right(v___x_4125_, v___x_4126_);
v_fold_4128_ = lean_uint64_xor(v___x_4125_, v___x_4127_);
v___x_4129_ = 16ULL;
v___x_4130_ = lean_uint64_shift_right(v_fold_4128_, v___x_4129_);
v___x_4131_ = lean_uint64_xor(v_fold_4128_, v___x_4130_);
v___x_4132_ = lean_uint64_to_usize(v___x_4131_);
v___x_4133_ = lean_usize_of_nat(v___x_4124_);
v___x_4134_ = ((size_t)1ULL);
v___x_4135_ = lean_usize_sub(v___x_4133_, v___x_4134_);
v___x_4136_ = lean_usize_land(v___x_4132_, v___x_4135_);
v___x_4137_ = lean_usize_to_nat(v___x_4136_);
v___x_4138_ = lean_box(0);
v___x_4139_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__7___redArg(v_m_4121_, v_query_4122_, v___x_4138_, v___x_4124_, v___x_4137_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg___boxed(lean_object* v_m_4140_, lean_object* v_query_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_m_4140_, v_query_4141_);
lean_dec_ref(v_query_4141_);
lean_dec_ref(v_m_4140_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3_spec__5___redArg(lean_object* v_m_4143_, lean_object* v_query_4144_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_m_4143_, v_query_4144_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_index_4146_; lean_object* v_key_4147_; lean_object* v_value_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
v_index_4146_ = lean_ctor_get(v___x_4145_, 0);
v_key_4147_ = lean_ctor_get(v___x_4145_, 1);
v_value_4148_ = lean_ctor_get(v___x_4145_, 2);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4145_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_value_4148_);
lean_inc(v_key_4147_);
lean_inc(v_index_4146_);
lean_dec(v___x_4145_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_index_4146_);
lean_ctor_set(v_reuseFailAlloc_4154_, 1, v_key_4147_);
lean_ctor_set(v_reuseFailAlloc_4154_, 2, v_value_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
else
{
lean_object* v___x_4156_; 
lean_dec(v___x_4145_);
v___x_4156_ = lean_box(1);
return v___x_4156_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_m_4157_, lean_object* v_query_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3_spec__5___redArg(v_m_4157_, v_query_4158_);
lean_dec_ref(v_query_4158_);
lean_dec_ref(v_m_4157_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3___redArg(lean_object* v_m_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v___x_4162_; 
v___x_4162_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3_spec__5___redArg(v_m_4160_, v_a_4161_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_value_4163_; lean_object* v___x_4164_; 
v_value_4163_ = lean_ctor_get(v___x_4162_, 2);
lean_inc(v_value_4163_);
lean_dec_ref_known(v___x_4162_, 3);
v___x_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4164_, 0, v_value_4163_);
return v___x_4164_;
}
else
{
lean_object* v___x_4165_; 
v___x_4165_ = lean_box(0);
return v___x_4165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3___redArg___boxed(lean_object* v_m_4166_, lean_object* v_a_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3___redArg(v_m_4166_, v_a_4167_);
lean_dec_ref(v_a_4167_);
lean_dec_ref(v_m_4166_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9_spec__15___redArg(lean_object* v_b_4169_, lean_object* v_acc_4170_, lean_object* v_i_4171_){
_start:
{
lean_object* v___y_4173_; lean_object* v_keyArray_4181_; lean_object* v_valueArray_4182_; lean_object* v___x_4183_; uint8_t v___x_4184_; 
v_keyArray_4181_ = lean_ctor_get(v_b_4169_, 1);
v_valueArray_4182_ = lean_ctor_get(v_b_4169_, 2);
v___x_4183_ = lean_array_get_size(v_keyArray_4181_);
v___x_4184_ = lean_nat_dec_lt(v_i_4171_, v___x_4183_);
if (v___x_4184_ == 0)
{
lean_dec(v_i_4171_);
return v_acc_4170_;
}
else
{
lean_object* v___x_4185_; uint8_t v_isSome_4186_; 
v___x_4185_ = lean_array_fget_borrowed(v_keyArray_4181_, v_i_4171_);
v_isSome_4186_ = lean_noption_is_some(v___x_4185_);
if (v_isSome_4186_ == 0)
{
goto v___jp_4177_;
}
else
{
lean_object* v___x_4187_; uint8_t v_isSome_4188_; 
v___x_4187_ = lean_array_fget_borrowed(v_valueArray_4182_, v_i_4171_);
v_isSome_4188_ = lean_noption_is_some(v___x_4187_);
if (v_isSome_4188_ == 0)
{
goto v___jp_4177_;
}
else
{
lean_object* v_val_4189_; lean_object* v_val_4190_; lean_object* v_i_4192_; lean_object* v___x_4197_; 
lean_inc(v___x_4185_);
v_val_4189_ = lean_noption_get(v___x_4185_);
lean_inc(v___x_4187_);
v_val_4190_ = lean_noption_get(v___x_4187_);
v___x_4197_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_acc_4170_, v_val_4189_);
switch(lean_obj_tag(v___x_4197_))
{
case 0:
{
lean_object* v_index_4198_; lean_object* v_size_4199_; lean_object* v___x_4200_; 
v_index_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_index_4198_);
lean_dec_ref_known(v___x_4197_, 3);
v_size_4199_ = lean_ctor_get(v_acc_4170_, 0);
lean_inc(v_size_4199_);
v___x_4200_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_4170_, v_size_4199_, v_index_4198_, v_val_4189_, v_val_4190_);
lean_dec(v_index_4198_);
v___y_4173_ = v___x_4200_;
goto v___jp_4172_;
}
case 1:
{
lean_object* v_index_4201_; 
v_index_4201_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_index_4201_);
lean_dec_ref_known(v___x_4197_, 1);
v_i_4192_ = v_index_4201_;
goto v___jp_4191_;
}
default: 
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = lean_unsigned_to_nat(0u);
v___x_4203_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_4170_, v___x_4202_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_index_4204_; 
v_index_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_index_4204_);
lean_dec_ref_known(v___x_4203_, 1);
v_i_4192_ = v_index_4204_;
goto v___jp_4191_;
}
else
{
lean_dec(v_val_4190_);
lean_dec(v_val_4189_);
v___y_4173_ = v_acc_4170_;
goto v___jp_4172_;
}
}
}
v___jp_4191_:
{
lean_object* v_size_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v_size_4193_ = lean_ctor_get(v_acc_4170_, 0);
v___x_4194_ = lean_unsigned_to_nat(1u);
v___x_4195_ = lean_nat_add(v_size_4193_, v___x_4194_);
v___x_4196_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_4170_, v___x_4195_, v_i_4192_, v_val_4189_, v_val_4190_);
lean_dec(v_i_4192_);
v___y_4173_ = v___x_4196_;
goto v___jp_4172_;
}
}
}
}
v___jp_4172_:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4174_ = lean_unsigned_to_nat(1u);
v___x_4175_ = lean_nat_add(v_i_4171_, v___x_4174_);
lean_dec(v_i_4171_);
v_acc_4170_ = v___y_4173_;
v_i_4171_ = v___x_4175_;
goto _start;
}
v___jp_4177_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = lean_unsigned_to_nat(1u);
v___x_4179_ = lean_nat_add(v_i_4171_, v___x_4178_);
lean_dec(v_i_4171_);
v_i_4171_ = v___x_4179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9_spec__15___redArg___boxed(lean_object* v_b_4205_, lean_object* v_acc_4206_, lean_object* v_i_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9_spec__15___redArg(v_b_4205_, v_acc_4206_, v_i_4207_);
lean_dec_ref(v_b_4205_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9___redArg(lean_object* v_init_4209_, lean_object* v_b_4210_){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = lean_unsigned_to_nat(0u);
v___x_4212_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9_spec__15___redArg(v_b_4210_, v_init_4209_, v___x_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_init_4213_, lean_object* v_b_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9___redArg(v_init_4213_, v_b_4214_);
lean_dec_ref(v_b_4214_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5___redArg(lean_object* v_m_4216_){
_start:
{
lean_object* v_keyArray_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v_cellCount_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v_target_4224_; lean_object* v___x_4225_; 
v_keyArray_4217_ = lean_ctor_get(v_m_4216_, 1);
v___x_4218_ = lean_array_get_size(v_keyArray_4217_);
v___x_4219_ = lean_unsigned_to_nat(2u);
v_cellCount_4220_ = lean_nat_mul(v___x_4218_, v___x_4219_);
v___x_4221_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_4220_);
v___x_4222_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_4220_);
v___x_4223_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_4220_);
v_target_4224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_4224_, 0, v___x_4221_);
lean_ctor_set(v_target_4224_, 1, v___x_4222_);
lean_ctor_set(v_target_4224_, 2, v___x_4223_);
v___x_4225_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9___redArg(v_target_4224_, v_m_4216_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5___redArg___boxed(lean_object* v_m_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5___redArg(v_m_4226_);
lean_dec_ref(v_m_4226_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object* v_g_4228_, lean_object* v_e_4229_, lean_object* v_a_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v_i_4244_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v_i_4265_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v_a_4284_; lean_object* v_fst_4285_; lean_object* v___y_4318_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = lean_st_ref_get(v_a_4230_);
v___x_4322_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3___redArg(v___x_4321_, v_e_4229_);
lean_dec(v___x_4321_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v___x_4323_; 
lean_inc_ref(v_g_4228_);
lean_inc(v___y_4233_);
lean_inc_ref(v___y_4232_);
lean_inc_ref(v_e_4229_);
v___x_4323_ = lean_apply_5(v_g_4228_, v_e_4229_, v___y_4231_, v___y_4232_, v___y_4233_, lean_box(0));
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v_fst_4325_; lean_object* v_snd_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4371_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4323_, 1);
v_fst_4325_ = lean_ctor_get(v_a_4324_, 0);
v_snd_4326_ = lean_ctor_get(v_a_4324_, 1);
v_isSharedCheck_4371_ = !lean_is_exclusive(v_a_4324_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4328_ = v_a_4324_;
v_isShared_4329_ = v_isSharedCheck_4371_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_snd_4326_);
lean_inc(v_fst_4325_);
lean_dec(v_a_4324_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4371_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v_d_4331_; lean_object* v_b_4332_; lean_object* v___y_4333_; uint8_t v___x_4338_; 
v___x_4338_ = lean_unbox(v_fst_4325_);
lean_dec(v_fst_4325_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; lean_object* v___x_4341_; 
lean_dec_ref(v_g_4228_);
v___x_4339_ = lean_box(0);
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v___x_4339_);
v___x_4341_ = v___x_4328_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4339_);
lean_ctor_set(v_reuseFailAlloc_4342_, 1, v_snd_4326_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
v_a_4284_ = v___x_4341_;
v_fst_4285_ = v___x_4339_;
goto v___jp_4283_;
}
}
else
{
switch(lean_obj_tag(v_e_4229_))
{
case 7:
{
lean_object* v_binderType_4343_; lean_object* v_body_4344_; 
lean_del_object(v___x_4328_);
v_binderType_4343_ = lean_ctor_get(v_e_4229_, 1);
v_body_4344_ = lean_ctor_get(v_e_4229_, 2);
lean_inc_ref(v_body_4344_);
lean_inc_ref(v_binderType_4343_);
v_d_4331_ = v_binderType_4343_;
v_b_4332_ = v_body_4344_;
v___y_4333_ = v_a_4230_;
goto v___jp_4330_;
}
case 6:
{
lean_object* v_binderType_4345_; lean_object* v_body_4346_; 
lean_del_object(v___x_4328_);
v_binderType_4345_ = lean_ctor_get(v_e_4229_, 1);
v_body_4346_ = lean_ctor_get(v_e_4229_, 2);
lean_inc_ref(v_body_4346_);
lean_inc_ref(v_binderType_4345_);
v_d_4331_ = v_binderType_4345_;
v_b_4332_ = v_body_4346_;
v___y_4333_ = v_a_4230_;
goto v___jp_4330_;
}
case 8:
{
lean_object* v_type_4347_; lean_object* v_value_4348_; lean_object* v_body_4349_; lean_object* v___x_4350_; 
lean_del_object(v___x_4328_);
v_type_4347_ = lean_ctor_get(v_e_4229_, 1);
v_value_4348_ = lean_ctor_get(v_e_4229_, 2);
v_body_4349_ = lean_ctor_get(v_e_4229_, 3);
lean_inc_ref(v_type_4347_);
lean_inc_ref(v_g_4228_);
v___x_4350_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v_g_4228_, v_type_4347_, v_a_4230_, v_snd_4326_, v___y_4232_, v___y_4233_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v_snd_4352_; lean_object* v___x_4353_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4350_, 1);
v_snd_4352_ = lean_ctor_get(v_a_4351_, 1);
lean_inc(v_snd_4352_);
lean_dec(v_a_4351_);
lean_inc_ref(v_value_4348_);
lean_inc_ref(v_g_4228_);
v___x_4353_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v_g_4228_, v_value_4348_, v_a_4230_, v_snd_4352_, v___y_4232_, v___y_4233_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v_snd_4355_; lean_object* v___x_4356_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v___x_4353_, 1);
v_snd_4355_ = lean_ctor_get(v_a_4354_, 1);
lean_inc(v_snd_4355_);
lean_dec(v_a_4354_);
lean_inc_ref(v_body_4349_);
v___x_4356_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v_g_4228_, v_body_4349_, v_a_4230_, v_snd_4355_, v___y_4232_, v___y_4233_);
v___y_4318_ = v___x_4356_;
goto v___jp_4317_;
}
else
{
lean_dec_ref(v_g_4228_);
v___y_4318_ = v___x_4353_;
goto v___jp_4317_;
}
}
else
{
lean_dec_ref(v_g_4228_);
v___y_4318_ = v___x_4350_;
goto v___jp_4317_;
}
}
case 5:
{
lean_object* v_fn_4357_; lean_object* v_arg_4358_; lean_object* v___x_4359_; 
lean_del_object(v___x_4328_);
v_fn_4357_ = lean_ctor_get(v_e_4229_, 0);
v_arg_4358_ = lean_ctor_get(v_e_4229_, 1);
lean_inc_ref(v_fn_4357_);
lean_inc_ref(v_g_4228_);
v___x_4359_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v_g_4228_, v_fn_4357_, v_a_4230_, v_snd_4326_, v___y_4232_, v___y_4233_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v_snd_4361_; lean_object* v___x_4362_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_a_4360_);
lean_dec_ref_known(v___x_4359_, 1);
v_snd_4361_ = lean_ctor_get(v_a_4360_, 1);
lean_inc(v_snd_4361_);
lean_dec(v_a_4360_);
lean_inc_ref(v_arg_4358_);
v___x_4362_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v_g_4228_, v_arg_4358_, v_a_4230_, v_snd_4361_, v___y_4232_, v___y_4233_);
v___y_4318_ = v___x_4362_;
goto v___jp_4317_;
}
else
{
lean_dec_ref(v_g_4228_);
v___y_4318_ = v___x_4359_;
goto v___jp_4317_;
}
}
case 10:
{
lean_object* v_expr_4363_; lean_object* v___x_4364_; 
lean_del_object(v___x_4328_);
v_expr_4363_ = lean_ctor_get(v_e_4229_, 1);
lean_inc_ref(v_expr_4363_);
v___x_4364_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v_g_4228_, v_expr_4363_, v_a_4230_, v_snd_4326_, v___y_4232_, v___y_4233_);
v___y_4318_ = v___x_4364_;
goto v___jp_4317_;
}
case 11:
{
lean_object* v_struct_4365_; lean_object* v___x_4366_; 
lean_del_object(v___x_4328_);
v_struct_4365_ = lean_ctor_get(v_e_4229_, 2);
lean_inc_ref(v_struct_4365_);
v___x_4366_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v_g_4228_, v_struct_4365_, v_a_4230_, v_snd_4326_, v___y_4232_, v___y_4233_);
v___y_4318_ = v___x_4366_;
goto v___jp_4317_;
}
default: 
{
lean_object* v___x_4367_; lean_object* v___x_4369_; 
lean_dec_ref(v_g_4228_);
v___x_4367_ = lean_box(0);
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v___x_4367_);
v___x_4369_ = v___x_4328_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_snd_4326_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
v_a_4284_ = v___x_4369_;
v_fst_4285_ = v___x_4367_;
goto v___jp_4283_;
}
}
}
}
v___jp_4330_:
{
lean_object* v___x_4334_; 
lean_inc_ref(v_g_4228_);
v___x_4334_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v_g_4228_, v_d_4331_, v___y_4333_, v_snd_4326_, v___y_4232_, v___y_4233_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; lean_object* v_snd_4336_; lean_object* v___x_4337_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4334_, 1);
v_snd_4336_ = lean_ctor_get(v_a_4335_, 1);
lean_inc(v_snd_4336_);
lean_dec(v_a_4335_);
v___x_4337_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v_g_4228_, v_b_4332_, v___y_4333_, v_snd_4336_, v___y_4232_, v___y_4233_);
v___y_4318_ = v___x_4337_;
goto v___jp_4317_;
}
else
{
lean_dec_ref(v_b_4332_);
lean_dec_ref(v_g_4228_);
v___y_4318_ = v___x_4334_;
goto v___jp_4317_;
}
}
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_dec_ref(v_e_4229_);
lean_dec_ref(v_g_4228_);
v_a_4372_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4323_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4323_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
else
{
lean_object* v_val_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4388_; 
lean_dec_ref(v_e_4229_);
lean_dec_ref(v_g_4228_);
v_val_4380_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4382_ = v___x_4322_;
v_isShared_4383_ = v_isSharedCheck_4388_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_val_4380_);
lean_dec(v___x_4322_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4388_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; lean_object* v___x_4386_; 
v___x_4384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4384_, 0, v_val_4380_);
lean_ctor_set(v___x_4384_, 1, v___y_4231_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set_tag(v___x_4382_, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4384_);
v___x_4386_ = v___x_4382_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4384_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
v___jp_4235_:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; 
v___x_4238_ = lean_st_ref_put(v_a_4230_, v___y_4237_);
v___x_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4239_, 0, v___y_4236_);
return v___x_4239_;
}
v___jp_4240_:
{
lean_object* v_size_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v_size_4245_ = lean_ctor_get(v___y_4241_, 0);
v___x_4246_ = lean_unsigned_to_nat(1u);
v___x_4247_ = lean_nat_add(v_size_4245_, v___x_4246_);
v___x_4248_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4241_, v___x_4247_, v_i_4244_, v_e_4229_, v___y_4242_);
lean_dec(v_i_4244_);
v___y_4236_ = v___y_4243_;
v___y_4237_ = v___x_4248_;
goto v___jp_4235_;
}
v___jp_4249_:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v___y_4252_, v_e_4229_);
switch(lean_obj_tag(v___x_4253_))
{
case 0:
{
lean_object* v_index_4254_; lean_object* v_size_4255_; lean_object* v___x_4256_; 
v_index_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_index_4254_);
lean_dec_ref_known(v___x_4253_, 3);
v_size_4255_ = lean_ctor_get(v___y_4252_, 0);
lean_inc(v_size_4255_);
v___x_4256_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4252_, v_size_4255_, v_index_4254_, v_e_4229_, v___y_4250_);
lean_dec(v_index_4254_);
v___y_4236_ = v___y_4251_;
v___y_4237_ = v___x_4256_;
goto v___jp_4235_;
}
case 1:
{
lean_object* v_index_4257_; 
v_index_4257_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_index_4257_);
lean_dec_ref_known(v___x_4253_, 1);
v___y_4241_ = v___y_4252_;
v___y_4242_ = v___y_4250_;
v___y_4243_ = v___y_4251_;
v_i_4244_ = v_index_4257_;
goto v___jp_4240_;
}
default: 
{
lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4258_ = lean_unsigned_to_nat(0u);
v___x_4259_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4252_, v___x_4258_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_index_4260_; 
v_index_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_index_4260_);
lean_dec_ref_known(v___x_4259_, 1);
v___y_4241_ = v___y_4252_;
v___y_4242_ = v___y_4250_;
v___y_4243_ = v___y_4251_;
v_i_4244_ = v_index_4260_;
goto v___jp_4240_;
}
else
{
lean_dec_ref(v_e_4229_);
v___y_4236_ = v___y_4251_;
v___y_4237_ = v___y_4252_;
goto v___jp_4235_;
}
}
}
}
v___jp_4261_:
{
lean_object* v_size_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v_size_4266_ = lean_ctor_get(v___y_4262_, 0);
v___x_4267_ = lean_unsigned_to_nat(1u);
v___x_4268_ = lean_nat_add(v_size_4266_, v___x_4267_);
v___x_4269_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4262_, v___x_4268_, v_i_4265_, v_e_4229_, v___y_4263_);
lean_dec(v_i_4265_);
v___y_4236_ = v___y_4264_;
v___y_4237_ = v___x_4269_;
goto v___jp_4235_;
}
v___jp_4270_:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4274_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5___redArg(v___y_4272_);
lean_dec_ref(v___y_4272_);
v___x_4275_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v___x_4274_, v_e_4229_);
switch(lean_obj_tag(v___x_4275_))
{
case 0:
{
lean_object* v_index_4276_; lean_object* v_size_4277_; lean_object* v___x_4278_; 
v_index_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_index_4276_);
lean_dec_ref_known(v___x_4275_, 3);
v_size_4277_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_size_4277_);
v___x_4278_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4274_, v_size_4277_, v_index_4276_, v_e_4229_, v___y_4271_);
lean_dec(v_index_4276_);
v___y_4236_ = v___y_4273_;
v___y_4237_ = v___x_4278_;
goto v___jp_4235_;
}
case 1:
{
lean_object* v_index_4279_; 
v_index_4279_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_index_4279_);
lean_dec_ref_known(v___x_4275_, 1);
v___y_4262_ = v___x_4274_;
v___y_4263_ = v___y_4271_;
v___y_4264_ = v___y_4273_;
v_i_4265_ = v_index_4279_;
goto v___jp_4261_;
}
default: 
{
lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4280_ = lean_unsigned_to_nat(0u);
v___x_4281_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4274_, v___x_4280_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v_index_4282_; 
v_index_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_index_4282_);
lean_dec_ref_known(v___x_4281_, 1);
v___y_4262_ = v___x_4274_;
v___y_4263_ = v___y_4271_;
v___y_4264_ = v___y_4273_;
v_i_4265_ = v_index_4282_;
goto v___jp_4261_;
}
else
{
lean_dec_ref(v_e_4229_);
v___y_4236_ = v___y_4273_;
v___y_4237_ = v___x_4274_;
goto v___jp_4235_;
}
}
}
}
v___jp_4283_:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4286_ = lean_st_ref_take(v_a_4230_);
v___x_4287_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v___x_4286_, v_e_4229_);
switch(lean_obj_tag(v___x_4287_))
{
case 0:
{
lean_object* v_index_4288_; lean_object* v_size_4289_; lean_object* v___x_4290_; 
v_index_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_index_4288_);
lean_dec_ref_known(v___x_4287_, 3);
v_size_4289_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_size_4289_);
v___x_4290_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4286_, v_size_4289_, v_index_4288_, v_e_4229_, v_fst_4285_);
lean_dec(v_index_4288_);
v___y_4236_ = v_a_4284_;
v___y_4237_ = v___x_4290_;
goto v___jp_4235_;
}
case 1:
{
lean_object* v_index_4291_; lean_object* v_size_4292_; lean_object* v_keyArray_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; uint8_t v___x_4297_; 
v_index_4291_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_index_4291_);
lean_dec_ref_known(v___x_4287_, 1);
v_size_4292_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_size_4292_);
v_keyArray_4293_ = lean_ctor_get(v___x_4286_, 1);
lean_inc_ref(v_keyArray_4293_);
v___x_4294_ = lean_unsigned_to_nat(1u);
v___x_4295_ = lean_nat_add(v_size_4292_, v___x_4294_);
lean_dec(v_size_4292_);
v___x_4296_ = lean_array_get_size(v_keyArray_4293_);
lean_dec_ref(v_keyArray_4293_);
v___x_4297_ = lean_nat_dec_lt(v___x_4295_, v___x_4296_);
if (v___x_4297_ == 0)
{
lean_dec(v___x_4295_);
lean_dec(v_index_4291_);
v___y_4271_ = v_fst_4285_;
v___y_4272_ = v___x_4286_;
v___y_4273_ = v_a_4284_;
goto v___jp_4270_;
}
else
{
lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; uint8_t v___x_4302_; 
v___x_4298_ = lean_unsigned_to_nat(4u);
v___x_4299_ = lean_nat_mul(v___x_4295_, v___x_4298_);
v___x_4300_ = lean_unsigned_to_nat(3u);
v___x_4301_ = lean_nat_mul(v___x_4296_, v___x_4300_);
v___x_4302_ = lean_nat_dec_le(v___x_4299_, v___x_4301_);
lean_dec(v___x_4301_);
lean_dec(v___x_4299_);
if (v___x_4302_ == 0)
{
lean_dec(v___x_4295_);
lean_dec(v_index_4291_);
v___y_4271_ = v_fst_4285_;
v___y_4272_ = v___x_4286_;
v___y_4273_ = v_a_4284_;
goto v___jp_4270_;
}
else
{
lean_object* v___x_4303_; 
v___x_4303_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4286_, v___x_4295_, v_index_4291_, v_e_4229_, v_fst_4285_);
lean_dec(v_index_4291_);
v___y_4236_ = v_a_4284_;
v___y_4237_ = v___x_4303_;
goto v___jp_4235_;
}
}
}
default: 
{
lean_object* v_size_4304_; lean_object* v_keyArray_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v_size_4304_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_size_4304_);
v_keyArray_4305_ = lean_ctor_get(v___x_4286_, 1);
lean_inc_ref(v_keyArray_4305_);
v___x_4306_ = lean_unsigned_to_nat(1u);
v___x_4307_ = lean_nat_add(v_size_4304_, v___x_4306_);
lean_dec(v_size_4304_);
v___x_4308_ = lean_array_get_size(v_keyArray_4305_);
lean_dec_ref(v_keyArray_4305_);
v___x_4309_ = lean_nat_dec_lt(v___x_4307_, v___x_4308_);
if (v___x_4309_ == 0)
{
lean_object* v___x_4310_; 
lean_dec(v___x_4307_);
v___x_4310_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5___redArg(v___x_4286_);
lean_dec(v___x_4286_);
v___y_4250_ = v_fst_4285_;
v___y_4251_ = v_a_4284_;
v___y_4252_ = v___x_4310_;
goto v___jp_4249_;
}
else
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; uint8_t v___x_4315_; 
v___x_4311_ = lean_unsigned_to_nat(4u);
v___x_4312_ = lean_nat_mul(v___x_4307_, v___x_4311_);
lean_dec(v___x_4307_);
v___x_4313_ = lean_unsigned_to_nat(3u);
v___x_4314_ = lean_nat_mul(v___x_4308_, v___x_4313_);
v___x_4315_ = lean_nat_dec_le(v___x_4312_, v___x_4314_);
lean_dec(v___x_4314_);
lean_dec(v___x_4312_);
if (v___x_4315_ == 0)
{
lean_object* v___x_4316_; 
v___x_4316_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5___redArg(v___x_4286_);
lean_dec(v___x_4286_);
v___y_4250_ = v_fst_4285_;
v___y_4251_ = v_a_4284_;
v___y_4252_ = v___x_4316_;
goto v___jp_4249_;
}
else
{
v___y_4250_ = v_fst_4285_;
v___y_4251_ = v_a_4284_;
v___y_4252_ = v___x_4286_;
goto v___jp_4249_;
}
}
}
}
}
v___jp_4317_:
{
if (lean_obj_tag(v___y_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v_fst_4320_; 
v_a_4319_ = lean_ctor_get(v___y_4318_, 0);
lean_inc(v_a_4319_);
lean_dec_ref_known(v___y_4318_, 1);
v_fst_4320_ = lean_ctor_get(v_a_4319_, 0);
lean_inc(v_fst_4320_);
v_a_4284_ = v_a_4319_;
v_fst_4285_ = v_fst_4320_;
goto v___jp_4283_;
}
else
{
lean_dec_ref(v_e_4229_);
return v___y_4318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___boxed(lean_object* v_g_4389_, lean_object* v_e_4390_, lean_object* v_a_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v_g_4389_, v_e_4390_, v_a_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec(v_a_4391_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object* v_m_4397_, lean_object* v_a_4398_){
_start:
{
lean_object* v___x_4399_; 
v___x_4399_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_m_4397_, v_a_4398_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_value_4400_; lean_object* v___x_4401_; 
v_value_4400_ = lean_ctor_get(v___x_4399_, 2);
lean_inc(v_value_4400_);
lean_dec_ref_known(v___x_4399_, 3);
v___x_4401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4401_, 0, v_value_4400_);
return v___x_4401_;
}
else
{
lean_object* v___x_4402_; 
v___x_4402_ = lean_box(0);
return v___x_4402_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object* v_m_4403_, lean_object* v_a_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_4403_, v_a_4404_);
lean_dec(v_a_4404_);
lean_dec_ref(v_m_4403_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9_spec__14___redArg(lean_object* v_b_4406_, lean_object* v_acc_4407_, lean_object* v_i_4408_){
_start:
{
lean_object* v___y_4410_; lean_object* v_keyArray_4418_; lean_object* v_valueArray_4419_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v_keyArray_4418_ = lean_ctor_get(v_b_4406_, 1);
v_valueArray_4419_ = lean_ctor_get(v_b_4406_, 2);
v___x_4420_ = lean_array_get_size(v_keyArray_4418_);
v___x_4421_ = lean_nat_dec_lt(v_i_4408_, v___x_4420_);
if (v___x_4421_ == 0)
{
lean_dec(v_i_4408_);
return v_acc_4407_;
}
else
{
lean_object* v___x_4422_; uint8_t v_isSome_4423_; 
v___x_4422_ = lean_array_fget_borrowed(v_keyArray_4418_, v_i_4408_);
v_isSome_4423_ = lean_noption_is_some(v___x_4422_);
if (v_isSome_4423_ == 0)
{
goto v___jp_4414_;
}
else
{
lean_object* v___x_4424_; uint8_t v_isSome_4425_; 
v___x_4424_ = lean_array_fget_borrowed(v_valueArray_4419_, v_i_4408_);
v_isSome_4425_ = lean_noption_is_some(v___x_4424_);
if (v_isSome_4425_ == 0)
{
goto v___jp_4414_;
}
else
{
lean_object* v_val_4426_; lean_object* v_val_4427_; lean_object* v_i_4429_; lean_object* v___x_4434_; 
lean_inc(v___x_4422_);
v_val_4426_ = lean_noption_get(v___x_4422_);
lean_inc(v___x_4424_);
v_val_4427_ = lean_noption_get(v___x_4424_);
v___x_4434_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v_acc_4407_, v_val_4426_);
switch(lean_obj_tag(v___x_4434_))
{
case 0:
{
lean_object* v_index_4435_; lean_object* v_size_4436_; lean_object* v___x_4437_; 
v_index_4435_ = lean_ctor_get(v___x_4434_, 0);
lean_inc(v_index_4435_);
lean_dec_ref_known(v___x_4434_, 3);
v_size_4436_ = lean_ctor_get(v_acc_4407_, 0);
lean_inc(v_size_4436_);
v___x_4437_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_4407_, v_size_4436_, v_index_4435_, v_val_4426_, v_val_4427_);
lean_dec(v_index_4435_);
v___y_4410_ = v___x_4437_;
goto v___jp_4409_;
}
case 1:
{
lean_object* v_index_4438_; 
v_index_4438_ = lean_ctor_get(v___x_4434_, 0);
lean_inc(v_index_4438_);
lean_dec_ref_known(v___x_4434_, 1);
v_i_4429_ = v_index_4438_;
goto v___jp_4428_;
}
default: 
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4439_ = lean_unsigned_to_nat(0u);
v___x_4440_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_4407_, v___x_4439_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_index_4441_; 
v_index_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_index_4441_);
lean_dec_ref_known(v___x_4440_, 1);
v_i_4429_ = v_index_4441_;
goto v___jp_4428_;
}
else
{
lean_dec(v_val_4427_);
lean_dec(v_val_4426_);
v___y_4410_ = v_acc_4407_;
goto v___jp_4409_;
}
}
}
v___jp_4428_:
{
lean_object* v_size_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v_size_4430_ = lean_ctor_get(v_acc_4407_, 0);
v___x_4431_ = lean_unsigned_to_nat(1u);
v___x_4432_ = lean_nat_add(v_size_4430_, v___x_4431_);
v___x_4433_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_4407_, v___x_4432_, v_i_4429_, v_val_4426_, v_val_4427_);
lean_dec(v_i_4429_);
v___y_4410_ = v___x_4433_;
goto v___jp_4409_;
}
}
}
}
v___jp_4409_:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = lean_unsigned_to_nat(1u);
v___x_4412_ = lean_nat_add(v_i_4408_, v___x_4411_);
lean_dec(v_i_4408_);
v_acc_4407_ = v___y_4410_;
v_i_4408_ = v___x_4412_;
goto _start;
}
v___jp_4414_:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4415_ = lean_unsigned_to_nat(1u);
v___x_4416_ = lean_nat_add(v_i_4408_, v___x_4415_);
lean_dec(v_i_4408_);
v_i_4408_ = v___x_4416_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9_spec__14___redArg___boxed(lean_object* v_b_4442_, lean_object* v_acc_4443_, lean_object* v_i_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9_spec__14___redArg(v_b_4442_, v_acc_4443_, v_i_4444_);
lean_dec_ref(v_b_4442_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9___redArg(lean_object* v_init_4446_, lean_object* v_b_4447_){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4448_ = lean_unsigned_to_nat(0u);
v___x_4449_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9_spec__14___redArg(v_b_4447_, v_init_4446_, v___x_4448_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9___redArg___boxed(lean_object* v_init_4450_, lean_object* v_b_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9___redArg(v_init_4450_, v_b_4451_);
lean_dec_ref(v_b_4451_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(lean_object* v_m_4453_){
_start:
{
lean_object* v_keyArray_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v_cellCount_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v_target_4461_; lean_object* v___x_4462_; 
v_keyArray_4454_ = lean_ctor_get(v_m_4453_, 1);
v___x_4455_ = lean_array_get_size(v_keyArray_4454_);
v___x_4456_ = lean_unsigned_to_nat(2u);
v_cellCount_4457_ = lean_nat_mul(v___x_4455_, v___x_4456_);
v___x_4458_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_4457_);
v___x_4459_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_4457_);
v___x_4460_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_4457_);
v_target_4461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_4461_, 0, v___x_4458_);
lean_ctor_set(v_target_4461_, 1, v___x_4459_);
lean_ctor_set(v_target_4461_, 2, v___x_4460_);
v___x_4462_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9___redArg(v_target_4461_, v_m_4453_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg___boxed(lean_object* v_m_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(v_m_4463_);
lean_dec_ref(v_m_4463_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object* v___x_4465_, lean_object* v_m_4466_, lean_object* v_e_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
uint8_t v___x_26540__boxed_4472_; lean_object* v_res_4473_; 
v___x_26540__boxed_4472_ = lean_unbox(v___x_4465_);
v_res_4473_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(v___x_26540__boxed_4472_, v_m_4466_, v_e_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec_ref(v_e_4467_);
return v_res_4473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1(void){
_start:
{
lean_object* v_cellCount_4474_; lean_object* v___x_4475_; 
v_cellCount_4474_ = lean_unsigned_to_nat(16u);
v___x_4475_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_4474_);
return v___x_4475_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0(void){
_start:
{
lean_object* v_cellCount_4476_; lean_object* v___x_4477_; 
v_cellCount_4476_ = lean_unsigned_to_nat(16u);
v___x_4477_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_4476_);
return v___x_4477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2(void){
_start:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4478_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1);
v___x_4479_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0);
v___x_4480_ = lean_unsigned_to_nat(0u);
v___x_4481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4480_);
lean_ctor_set(v___x_4481_, 1, v___x_4479_);
lean_ctor_set(v___x_4481_, 2, v___x_4478_);
return v___x_4481_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6(void){
_start:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4485_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5));
v___x_4486_ = lean_unsigned_to_nat(4u);
v___x_4487_ = lean_unsigned_to_nat(384u);
v___x_4488_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4));
v___x_4489_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3));
v___x_4490_ = l_mkPanicMessageWithDecl(v___x_4489_, v___x_4488_, v___x_4487_, v___x_4486_, v___x_4485_);
return v___x_4490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8(void){
_start:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4492_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7));
v___x_4493_ = l_Lean_stringToMessageData(v___x_4492_);
return v___x_4493_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14(void){
_start:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4502_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11));
v___x_4503_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13));
v___x_4504_ = l_Lean_Name_append(v___x_4503_, v___x_4502_);
return v___x_4504_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16(void){
_start:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4506_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15));
v___x_4507_ = l_Lean_stringToMessageData(v___x_4506_);
return v___x_4507_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__18(void){
_start:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4509_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17));
v___x_4510_ = l_Lean_stringToMessageData(v___x_4509_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(lean_object* v_m_4511_, lean_object* v_fvarId_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v___x_4517_; 
v___x_4517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_4511_, v_fvarId_4512_);
if (lean_obj_tag(v___x_4517_) == 1)
{
lean_object* v_val_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4780_; 
v_val_4518_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4520_ = v___x_4517_;
v_isShared_4521_ = v_isSharedCheck_4780_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_val_4518_);
lean_dec(v___x_4517_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4780_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v_fst_4522_; lean_object* v_snd_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4779_; 
v_fst_4522_ = lean_ctor_get(v_val_4518_, 0);
v_snd_4523_ = lean_ctor_get(v_val_4518_, 1);
v_isSharedCheck_4779_ = !lean_is_exclusive(v_val_4518_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4525_ = v_val_4518_;
v_isShared_4526_ = v_isSharedCheck_4779_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_snd_4523_);
lean_inc(v_fst_4522_);
lean_dec(v_val_4518_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4779_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v_tempMark_4542_; lean_object* v_doneMark_4543_; lean_object* v___x_4544_; lean_object* v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v_i_4551_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v_i_4576_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; uint8_t v___x_4596_; 
v_tempMark_4542_ = lean_ctor_get(v_a_4513_, 0);
v_doneMark_4543_ = lean_ctor_get(v_a_4513_, 1);
v___x_4544_ = l_Lean_LocalDecl_fvarId(v_fst_4522_);
v___x_4596_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_doneMark_4543_, v___x_4544_);
if (v___x_4596_ == 0)
{
lean_object* v_options_4597_; lean_object* v_inheritedTraceOptions_4598_; uint8_t v_hasTrace_4599_; uint8_t v___x_4600_; lean_object* v___x_4601_; lean_object* v___f_4602_; lean_object* v___y_4604_; lean_object* v___y_4605_; lean_object* v___y_4606_; lean_object* v___y_4607_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v_i_4665_; lean_object* v___y_4671_; lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v___y_4675_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v_i_4691_; lean_object* v___y_4697_; lean_object* v___y_4698_; lean_object* v___y_4699_; lean_object* v___y_4700_; lean_object* v___y_4701_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4713_; lean_object* v___y_4744_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4751_; lean_object* v_tempMark_4752_; lean_object* v___y_4753_; lean_object* v___y_4754_; 
v_options_4597_ = lean_ctor_get(v_a_4514_, 2);
v_inheritedTraceOptions_4598_ = lean_ctor_get(v_a_4514_, 13);
v_hasTrace_4599_ = lean_ctor_get_uint8(v_options_4597_, sizeof(void*)*1);
v___x_4600_ = 1;
v___x_4601_ = lean_box(v___x_4600_);
v___f_4602_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4602_, 0, v___x_4601_);
lean_closure_set(v___f_4602_, 1, v_m_4511_);
if (v_hasTrace_4599_ == 0)
{
lean_inc_ref(v_tempMark_4542_);
v___y_4751_ = v_a_4513_;
v_tempMark_4752_ = v_tempMark_4542_;
v___y_4753_ = v_a_4514_;
v___y_4754_ = v_a_4515_;
goto v___jp_4750_;
}
else
{
lean_object* v___x_4760_; lean_object* v___x_4761_; uint8_t v___x_4762_; 
v___x_4760_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11));
v___x_4761_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14);
v___x_4762_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4598_, v_options_4597_, v___x_4761_);
if (v___x_4762_ == 0)
{
lean_inc_ref(v_tempMark_4542_);
v___y_4751_ = v_a_4513_;
v_tempMark_4752_ = v_tempMark_4542_;
v___y_4753_ = v_a_4514_;
v___y_4754_ = v_a_4515_;
goto v___jp_4750_;
}
else
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4763_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16);
lean_inc(v___x_4544_);
v___x_4764_ = l_Lean_mkFVar(v___x_4544_);
v___x_4765_ = l_Lean_MessageData_ofExpr(v___x_4764_);
v___x_4766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4763_);
lean_ctor_set(v___x_4766_, 1, v___x_4765_);
v___x_4767_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__18, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__18_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__18);
v___x_4768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4768_, 0, v___x_4766_);
lean_ctor_set(v___x_4768_, 1, v___x_4767_);
v___x_4769_ = l_Lean_LocalDecl_type(v_fst_4522_);
v___x_4770_ = l_Lean_MessageData_ofExpr(v___x_4769_);
v___x_4771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4768_);
lean_ctor_set(v___x_4771_, 1, v___x_4770_);
v___x_4772_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7(v___x_4760_, v___x_4771_, v_a_4513_, v_a_4514_, v_a_4515_);
if (lean_obj_tag(v___x_4772_) == 0)
{
lean_object* v_a_4773_; lean_object* v_snd_4774_; lean_object* v_tempMark_4775_; 
v_a_4773_ = lean_ctor_get(v___x_4772_, 0);
lean_inc(v_a_4773_);
lean_dec_ref_known(v___x_4772_, 1);
v_snd_4774_ = lean_ctor_get(v_a_4773_, 1);
lean_inc(v_snd_4774_);
lean_dec(v_a_4773_);
v_tempMark_4775_ = lean_ctor_get(v_snd_4774_, 0);
lean_inc_ref(v_tempMark_4775_);
v___y_4751_ = v_snd_4774_;
v_tempMark_4752_ = v_tempMark_4775_;
v___y_4753_ = v_a_4514_;
v___y_4754_ = v_a_4515_;
goto v___jp_4750_;
}
else
{
lean_dec_ref(v___f_4602_);
lean_dec(v___x_4544_);
lean_del_object(v___x_4525_);
lean_dec(v_snd_4523_);
lean_dec(v_fst_4522_);
lean_del_object(v___x_4520_);
return v___x_4772_;
}
}
}
v___jp_4603_:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v_doneMark_4611_; lean_object* v_newDecls_4612_; lean_object* v_newArgs_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4657_; 
v___x_4608_ = lean_unsigned_to_nat(0u);
v___x_4609_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2);
v___x_4610_ = lean_st_mk_ref(v___x_4609_);
v_doneMark_4611_ = lean_ctor_get(v___y_4604_, 1);
v_newDecls_4612_ = lean_ctor_get(v___y_4604_, 2);
v_newArgs_4613_ = lean_ctor_get(v___y_4604_, 3);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___y_4604_);
if (v_isSharedCheck_4657_ == 0)
{
lean_object* v_unused_4658_; 
v_unused_4658_ = lean_ctor_get(v___y_4604_, 0);
lean_dec(v_unused_4658_);
v___x_4615_ = v___y_4604_;
v_isShared_4616_ = v_isSharedCheck_4657_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_newArgs_4613_);
lean_inc(v_newDecls_4612_);
lean_inc(v_doneMark_4611_);
lean_dec(v___y_4604_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4657_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v___y_4607_);
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___y_4607_);
lean_ctor_set(v_reuseFailAlloc_4656_, 1, v_doneMark_4611_);
lean_ctor_set(v_reuseFailAlloc_4656_, 2, v_newDecls_4612_);
lean_ctor_set(v_reuseFailAlloc_4656_, 3, v_newArgs_4613_);
v___x_4618_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4619_ = l_Lean_LocalDecl_type(v_fst_4522_);
v___x_4620_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(v___f_4602_, v___x_4619_, v___x_4610_, v___x_4618_, v___y_4606_, v___y_4605_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v_snd_4622_; lean_object* v___x_4623_; lean_object* v_tempMark_4624_; lean_object* v_doneMark_4625_; lean_object* v_newDecls_4626_; lean_object* v_newArgs_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc(v_a_4621_);
lean_dec_ref_known(v___x_4620_, 1);
v_snd_4622_ = lean_ctor_get(v_a_4621_, 1);
lean_inc(v_snd_4622_);
lean_dec(v_a_4621_);
v___x_4623_ = lean_st_ref_get(v___x_4610_);
lean_dec(v___x_4610_);
lean_dec(v___x_4623_);
v_tempMark_4624_ = lean_ctor_get(v_snd_4622_, 0);
lean_inc_ref(v_tempMark_4624_);
v_doneMark_4625_ = lean_ctor_get(v_snd_4622_, 1);
lean_inc_ref(v_doneMark_4625_);
v_newDecls_4626_ = lean_ctor_get(v_snd_4622_, 2);
lean_inc_ref(v_newDecls_4626_);
v_newArgs_4627_ = lean_ctor_get(v_snd_4622_, 3);
lean_inc_ref(v_newArgs_4627_);
lean_dec(v_snd_4622_);
v___x_4628_ = lean_box(0);
v___x_4629_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v_doneMark_4625_, v___x_4544_);
switch(lean_obj_tag(v___x_4629_))
{
case 0:
{
lean_dec_ref_known(v___x_4629_, 3);
lean_dec(v___x_4544_);
v___y_4528_ = v_tempMark_4624_;
v___y_4529_ = v_newArgs_4627_;
v___y_4530_ = v___x_4628_;
v___y_4531_ = v_newDecls_4626_;
v___y_4532_ = v_doneMark_4625_;
goto v___jp_4527_;
}
case 1:
{
lean_object* v_index_4630_; lean_object* v_size_4631_; lean_object* v_keyArray_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; uint8_t v___x_4636_; 
v_index_4630_ = lean_ctor_get(v___x_4629_, 0);
lean_inc(v_index_4630_);
lean_dec_ref_known(v___x_4629_, 1);
v_size_4631_ = lean_ctor_get(v_doneMark_4625_, 0);
v_keyArray_4632_ = lean_ctor_get(v_doneMark_4625_, 1);
v___x_4633_ = lean_unsigned_to_nat(1u);
v___x_4634_ = lean_nat_add(v_size_4631_, v___x_4633_);
v___x_4635_ = lean_array_get_size(v_keyArray_4632_);
v___x_4636_ = lean_nat_dec_lt(v___x_4634_, v___x_4635_);
if (v___x_4636_ == 0)
{
lean_dec(v___x_4634_);
lean_dec(v_index_4630_);
v___y_4582_ = v_newDecls_4626_;
v___y_4583_ = v_tempMark_4624_;
v___y_4584_ = v___x_4628_;
v___y_4585_ = v_newArgs_4627_;
v___y_4586_ = v___x_4608_;
v___y_4587_ = v_doneMark_4625_;
goto v___jp_4581_;
}
else
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; uint8_t v___x_4641_; 
v___x_4637_ = lean_unsigned_to_nat(4u);
v___x_4638_ = lean_nat_mul(v___x_4634_, v___x_4637_);
v___x_4639_ = lean_unsigned_to_nat(3u);
v___x_4640_ = lean_nat_mul(v___x_4635_, v___x_4639_);
v___x_4641_ = lean_nat_dec_le(v___x_4638_, v___x_4640_);
lean_dec(v___x_4640_);
lean_dec(v___x_4638_);
if (v___x_4641_ == 0)
{
lean_dec(v___x_4634_);
lean_dec(v_index_4630_);
v___y_4582_ = v_newDecls_4626_;
v___y_4583_ = v_tempMark_4624_;
v___y_4584_ = v___x_4628_;
v___y_4585_ = v_newArgs_4627_;
v___y_4586_ = v___x_4608_;
v___y_4587_ = v_doneMark_4625_;
goto v___jp_4581_;
}
else
{
lean_object* v___x_4642_; 
v___x_4642_ = l_Std_DHashMap_Raw_setEntry___redArg(v_doneMark_4625_, v___x_4634_, v_index_4630_, v___x_4544_, v___x_4628_);
lean_dec(v_index_4630_);
v___y_4528_ = v_tempMark_4624_;
v___y_4529_ = v_newArgs_4627_;
v___y_4530_ = v___x_4628_;
v___y_4531_ = v_newDecls_4626_;
v___y_4532_ = v___x_4642_;
goto v___jp_4527_;
}
}
}
default: 
{
lean_object* v_size_4643_; lean_object* v_keyArray_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; uint8_t v___x_4648_; 
v_size_4643_ = lean_ctor_get(v_doneMark_4625_, 0);
v_keyArray_4644_ = lean_ctor_get(v_doneMark_4625_, 1);
v___x_4645_ = lean_unsigned_to_nat(1u);
v___x_4646_ = lean_nat_add(v_size_4643_, v___x_4645_);
v___x_4647_ = lean_array_get_size(v_keyArray_4644_);
v___x_4648_ = lean_nat_dec_lt(v___x_4646_, v___x_4647_);
if (v___x_4648_ == 0)
{
lean_object* v___x_4649_; 
lean_dec(v___x_4646_);
v___x_4649_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(v_doneMark_4625_);
lean_dec_ref(v_doneMark_4625_);
v___y_4557_ = v_tempMark_4624_;
v___y_4558_ = v___x_4628_;
v___y_4559_ = v_newArgs_4627_;
v___y_4560_ = v___x_4608_;
v___y_4561_ = v_newDecls_4626_;
v___y_4562_ = v___x_4649_;
goto v___jp_4556_;
}
else
{
lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; uint8_t v___x_4654_; 
v___x_4650_ = lean_unsigned_to_nat(4u);
v___x_4651_ = lean_nat_mul(v___x_4646_, v___x_4650_);
lean_dec(v___x_4646_);
v___x_4652_ = lean_unsigned_to_nat(3u);
v___x_4653_ = lean_nat_mul(v___x_4647_, v___x_4652_);
v___x_4654_ = lean_nat_dec_le(v___x_4651_, v___x_4653_);
lean_dec(v___x_4653_);
lean_dec(v___x_4651_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4655_; 
v___x_4655_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(v_doneMark_4625_);
lean_dec_ref(v_doneMark_4625_);
v___y_4557_ = v_tempMark_4624_;
v___y_4558_ = v___x_4628_;
v___y_4559_ = v_newArgs_4627_;
v___y_4560_ = v___x_4608_;
v___y_4561_ = v_newDecls_4626_;
v___y_4562_ = v___x_4655_;
goto v___jp_4556_;
}
else
{
v___y_4557_ = v_tempMark_4624_;
v___y_4558_ = v___x_4628_;
v___y_4559_ = v_newArgs_4627_;
v___y_4560_ = v___x_4608_;
v___y_4561_ = v_newDecls_4626_;
v___y_4562_ = v_doneMark_4625_;
goto v___jp_4556_;
}
}
}
}
}
else
{
lean_dec(v___x_4610_);
lean_dec(v___x_4544_);
lean_del_object(v___x_4525_);
lean_dec(v_snd_4523_);
lean_dec(v_fst_4522_);
lean_del_object(v___x_4520_);
return v___x_4620_;
}
}
}
}
v___jp_4659_:
{
lean_object* v_size_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v_size_4666_ = lean_ctor_get(v___y_4664_, 0);
v___x_4667_ = lean_unsigned_to_nat(1u);
v___x_4668_ = lean_nat_add(v_size_4666_, v___x_4667_);
lean_inc(v___x_4544_);
v___x_4669_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4664_, v___x_4668_, v_i_4665_, v___x_4544_, v___y_4663_);
lean_dec(v_i_4665_);
v___y_4604_ = v___y_4660_;
v___y_4605_ = v___y_4661_;
v___y_4606_ = v___y_4662_;
v___y_4607_ = v___x_4669_;
goto v___jp_4603_;
}
v___jp_4670_:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4676_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(v___y_4674_);
lean_dec_ref(v___y_4674_);
v___x_4677_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v___x_4676_, v___x_4544_);
switch(lean_obj_tag(v___x_4677_))
{
case 0:
{
lean_object* v_index_4678_; lean_object* v_size_4679_; lean_object* v___x_4680_; 
v_index_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_index_4678_);
lean_dec_ref_known(v___x_4677_, 3);
v_size_4679_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_size_4679_);
lean_inc(v___x_4544_);
v___x_4680_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4676_, v_size_4679_, v_index_4678_, v___x_4544_, v___y_4675_);
lean_dec(v_index_4678_);
v___y_4604_ = v___y_4671_;
v___y_4605_ = v___y_4672_;
v___y_4606_ = v___y_4673_;
v___y_4607_ = v___x_4680_;
goto v___jp_4603_;
}
case 1:
{
lean_object* v_index_4681_; 
v_index_4681_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_index_4681_);
lean_dec_ref_known(v___x_4677_, 1);
v___y_4660_ = v___y_4671_;
v___y_4661_ = v___y_4672_;
v___y_4662_ = v___y_4673_;
v___y_4663_ = v___y_4675_;
v___y_4664_ = v___x_4676_;
v_i_4665_ = v_index_4681_;
goto v___jp_4659_;
}
default: 
{
lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4682_ = lean_unsigned_to_nat(0u);
v___x_4683_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4676_, v___x_4682_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_object* v_index_4684_; 
v_index_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc(v_index_4684_);
lean_dec_ref_known(v___x_4683_, 1);
v___y_4660_ = v___y_4671_;
v___y_4661_ = v___y_4672_;
v___y_4662_ = v___y_4673_;
v___y_4663_ = v___y_4675_;
v___y_4664_ = v___x_4676_;
v_i_4665_ = v_index_4684_;
goto v___jp_4659_;
}
else
{
v___y_4604_ = v___y_4671_;
v___y_4605_ = v___y_4672_;
v___y_4606_ = v___y_4673_;
v___y_4607_ = v___x_4676_;
goto v___jp_4603_;
}
}
}
}
v___jp_4685_:
{
lean_object* v_size_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v_size_4692_ = lean_ctor_get(v___y_4689_, 0);
v___x_4693_ = lean_unsigned_to_nat(1u);
v___x_4694_ = lean_nat_add(v_size_4692_, v___x_4693_);
lean_inc(v___x_4544_);
v___x_4695_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4689_, v___x_4694_, v_i_4691_, v___x_4544_, v___y_4690_);
lean_dec(v_i_4691_);
v___y_4604_ = v___y_4686_;
v___y_4605_ = v___y_4687_;
v___y_4606_ = v___y_4688_;
v___y_4607_ = v___x_4695_;
goto v___jp_4603_;
}
v___jp_4696_:
{
lean_object* v___x_4702_; 
v___x_4702_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v___y_4701_, v___x_4544_);
switch(lean_obj_tag(v___x_4702_))
{
case 0:
{
lean_object* v_index_4703_; lean_object* v_size_4704_; lean_object* v___x_4705_; 
v_index_4703_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_index_4703_);
lean_dec_ref_known(v___x_4702_, 3);
v_size_4704_ = lean_ctor_get(v___y_4701_, 0);
lean_inc(v_size_4704_);
lean_inc(v___x_4544_);
v___x_4705_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4701_, v_size_4704_, v_index_4703_, v___x_4544_, v___y_4700_);
lean_dec(v_index_4703_);
v___y_4604_ = v___y_4697_;
v___y_4605_ = v___y_4698_;
v___y_4606_ = v___y_4699_;
v___y_4607_ = v___x_4705_;
goto v___jp_4603_;
}
case 1:
{
lean_object* v_index_4706_; 
v_index_4706_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_index_4706_);
lean_dec_ref_known(v___x_4702_, 1);
v___y_4686_ = v___y_4697_;
v___y_4687_ = v___y_4698_;
v___y_4688_ = v___y_4699_;
v___y_4689_ = v___y_4701_;
v___y_4690_ = v___y_4700_;
v_i_4691_ = v_index_4706_;
goto v___jp_4685_;
}
default: 
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4707_ = lean_unsigned_to_nat(0u);
v___x_4708_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4701_, v___x_4707_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_index_4709_; 
v_index_4709_ = lean_ctor_get(v___x_4708_, 0);
lean_inc(v_index_4709_);
lean_dec_ref_known(v___x_4708_, 1);
v___y_4686_ = v___y_4697_;
v___y_4687_ = v___y_4698_;
v___y_4688_ = v___y_4699_;
v___y_4689_ = v___y_4701_;
v___y_4690_ = v___y_4700_;
v_i_4691_ = v_index_4709_;
goto v___jp_4685_;
}
else
{
v___y_4604_ = v___y_4697_;
v___y_4605_ = v___y_4698_;
v___y_4606_ = v___y_4699_;
v___y_4607_ = v___y_4701_;
goto v___jp_4603_;
}
}
}
}
v___jp_4710_:
{
lean_object* v_tempMark_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v_tempMark_4714_ = lean_ctor_get(v___y_4711_, 0);
v___x_4715_ = lean_box(0);
v___x_4716_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v_tempMark_4714_, v___x_4544_);
switch(lean_obj_tag(v___x_4716_))
{
case 0:
{
lean_inc_ref(v_tempMark_4714_);
lean_dec_ref_known(v___x_4716_, 3);
v___y_4604_ = v___y_4711_;
v___y_4605_ = v___y_4712_;
v___y_4606_ = v___y_4713_;
v___y_4607_ = v_tempMark_4714_;
goto v___jp_4603_;
}
case 1:
{
lean_object* v_index_4717_; lean_object* v_size_4718_; lean_object* v_keyArray_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; uint8_t v___x_4723_; 
v_index_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_index_4717_);
lean_dec_ref_known(v___x_4716_, 1);
v_size_4718_ = lean_ctor_get(v_tempMark_4714_, 0);
v_keyArray_4719_ = lean_ctor_get(v_tempMark_4714_, 1);
v___x_4720_ = lean_unsigned_to_nat(1u);
v___x_4721_ = lean_nat_add(v_size_4718_, v___x_4720_);
v___x_4722_ = lean_array_get_size(v_keyArray_4719_);
v___x_4723_ = lean_nat_dec_lt(v___x_4721_, v___x_4722_);
if (v___x_4723_ == 0)
{
lean_inc_ref(v_tempMark_4714_);
lean_dec(v___x_4721_);
lean_dec(v_index_4717_);
v___y_4671_ = v___y_4711_;
v___y_4672_ = v___y_4712_;
v___y_4673_ = v___y_4713_;
v___y_4674_ = v_tempMark_4714_;
v___y_4675_ = v___x_4715_;
goto v___jp_4670_;
}
else
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; 
v___x_4724_ = lean_unsigned_to_nat(4u);
v___x_4725_ = lean_nat_mul(v___x_4721_, v___x_4724_);
v___x_4726_ = lean_unsigned_to_nat(3u);
v___x_4727_ = lean_nat_mul(v___x_4722_, v___x_4726_);
v___x_4728_ = lean_nat_dec_le(v___x_4725_, v___x_4727_);
lean_dec(v___x_4727_);
lean_dec(v___x_4725_);
if (v___x_4728_ == 0)
{
lean_inc_ref(v_tempMark_4714_);
lean_dec(v___x_4721_);
lean_dec(v_index_4717_);
v___y_4671_ = v___y_4711_;
v___y_4672_ = v___y_4712_;
v___y_4673_ = v___y_4713_;
v___y_4674_ = v_tempMark_4714_;
v___y_4675_ = v___x_4715_;
goto v___jp_4670_;
}
else
{
lean_object* v___x_4729_; 
lean_inc(v___x_4544_);
lean_inc_ref(v_tempMark_4714_);
v___x_4729_ = l_Std_DHashMap_Raw_setEntry___redArg(v_tempMark_4714_, v___x_4721_, v_index_4717_, v___x_4544_, v___x_4715_);
lean_dec(v_index_4717_);
v___y_4604_ = v___y_4711_;
v___y_4605_ = v___y_4712_;
v___y_4606_ = v___y_4713_;
v___y_4607_ = v___x_4729_;
goto v___jp_4603_;
}
}
}
default: 
{
lean_object* v_size_4730_; lean_object* v_keyArray_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; uint8_t v___x_4735_; 
v_size_4730_ = lean_ctor_get(v_tempMark_4714_, 0);
v_keyArray_4731_ = lean_ctor_get(v_tempMark_4714_, 1);
v___x_4732_ = lean_unsigned_to_nat(1u);
v___x_4733_ = lean_nat_add(v_size_4730_, v___x_4732_);
v___x_4734_ = lean_array_get_size(v_keyArray_4731_);
v___x_4735_ = lean_nat_dec_lt(v___x_4733_, v___x_4734_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; 
lean_dec(v___x_4733_);
v___x_4736_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(v_tempMark_4714_);
v___y_4697_ = v___y_4711_;
v___y_4698_ = v___y_4712_;
v___y_4699_ = v___y_4713_;
v___y_4700_ = v___x_4715_;
v___y_4701_ = v___x_4736_;
goto v___jp_4696_;
}
else
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; uint8_t v___x_4741_; 
v___x_4737_ = lean_unsigned_to_nat(4u);
v___x_4738_ = lean_nat_mul(v___x_4733_, v___x_4737_);
lean_dec(v___x_4733_);
v___x_4739_ = lean_unsigned_to_nat(3u);
v___x_4740_ = lean_nat_mul(v___x_4734_, v___x_4739_);
v___x_4741_ = lean_nat_dec_le(v___x_4738_, v___x_4740_);
lean_dec(v___x_4740_);
lean_dec(v___x_4738_);
if (v___x_4741_ == 0)
{
lean_object* v___x_4742_; 
v___x_4742_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(v_tempMark_4714_);
v___y_4697_ = v___y_4711_;
v___y_4698_ = v___y_4712_;
v___y_4699_ = v___y_4713_;
v___y_4700_ = v___x_4715_;
v___y_4701_ = v___x_4742_;
goto v___jp_4696_;
}
else
{
lean_inc_ref(v_tempMark_4714_);
v___y_4697_ = v___y_4711_;
v___y_4698_ = v___y_4712_;
v___y_4699_ = v___y_4713_;
v___y_4700_ = v___x_4715_;
v___y_4701_ = v_tempMark_4714_;
goto v___jp_4696_;
}
}
}
}
}
v___jp_4743_:
{
uint8_t v___x_4747_; 
v___x_4747_ = l_Lean_LocalDecl_isLet(v_fst_4522_, v___x_4600_);
if (v___x_4747_ == 0)
{
v___y_4711_ = v___y_4744_;
v___y_4712_ = v___y_4746_;
v___y_4713_ = v___y_4745_;
goto v___jp_4710_;
}
else
{
if (v___x_4596_ == 0)
{
lean_object* v___x_4748_; lean_object* v___x_4749_; 
lean_dec_ref(v___f_4602_);
lean_dec(v___x_4544_);
lean_del_object(v___x_4525_);
lean_dec(v_snd_4523_);
lean_dec(v_fst_4522_);
lean_del_object(v___x_4520_);
v___x_4748_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6);
v___x_4749_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v___x_4748_, v___y_4744_, v___y_4745_, v___y_4746_);
return v___x_4749_;
}
else
{
v___y_4711_ = v___y_4744_;
v___y_4712_ = v___y_4746_;
v___y_4713_ = v___y_4745_;
goto v___jp_4710_;
}
}
}
v___jp_4750_:
{
uint8_t v___x_4755_; 
v___x_4755_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_tempMark_4752_, v___x_4544_);
lean_dec_ref(v_tempMark_4752_);
if (v___x_4755_ == 0)
{
v___y_4744_ = v___y_4751_;
v___y_4745_ = v___y_4753_;
v___y_4746_ = v___y_4754_;
goto v___jp_4743_;
}
else
{
lean_object* v___x_4756_; lean_object* v___x_4757_; 
lean_dec_ref(v___y_4751_);
v___x_4756_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__8);
v___x_4757_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___redArg(v___x_4756_, v___y_4753_, v___y_4754_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v_a_4758_; lean_object* v_snd_4759_; 
v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
lean_inc(v_a_4758_);
lean_dec_ref_known(v___x_4757_, 1);
v_snd_4759_ = lean_ctor_get(v_a_4758_, 1);
lean_inc(v_snd_4759_);
lean_dec(v_a_4758_);
v___y_4744_ = v_snd_4759_;
v___y_4745_ = v___y_4753_;
v___y_4746_ = v___y_4754_;
goto v___jp_4743_;
}
else
{
lean_dec_ref(v___f_4602_);
lean_dec(v___x_4544_);
lean_del_object(v___x_4525_);
lean_dec(v_snd_4523_);
lean_dec(v_fst_4522_);
lean_del_object(v___x_4520_);
return v___x_4757_;
}
}
}
}
else
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
lean_dec(v___x_4544_);
lean_del_object(v___x_4525_);
lean_dec(v_snd_4523_);
lean_dec(v_fst_4522_);
lean_del_object(v___x_4520_);
lean_dec_ref(v_m_4511_);
v___x_4776_ = lean_box(0);
v___x_4777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4776_);
lean_ctor_set(v___x_4777_, 1, v_a_4513_);
v___x_4778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4777_);
return v___x_4778_;
}
v___jp_4527_:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4537_; 
v___x_4533_ = lean_array_push(v___y_4531_, v_fst_4522_);
v___x_4534_ = lean_array_push(v___y_4529_, v_snd_4523_);
v___x_4535_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4535_, 0, v___y_4528_);
lean_ctor_set(v___x_4535_, 1, v___y_4532_);
lean_ctor_set(v___x_4535_, 2, v___x_4533_);
lean_ctor_set(v___x_4535_, 3, v___x_4534_);
if (v_isShared_4526_ == 0)
{
lean_ctor_set(v___x_4525_, 1, v___x_4535_);
lean_ctor_set(v___x_4525_, 0, v___y_4530_);
v___x_4537_ = v___x_4525_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___y_4530_);
lean_ctor_set(v_reuseFailAlloc_4541_, 1, v___x_4535_);
v___x_4537_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
lean_object* v___x_4539_; 
if (v_isShared_4521_ == 0)
{
lean_ctor_set_tag(v___x_4520_, 0);
lean_ctor_set(v___x_4520_, 0, v___x_4537_);
v___x_4539_ = v___x_4520_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v___x_4537_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
v___jp_4545_:
{
lean_object* v_size_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v_size_4552_ = lean_ctor_get(v___y_4547_, 0);
v___x_4553_ = lean_unsigned_to_nat(1u);
v___x_4554_ = lean_nat_add(v_size_4552_, v___x_4553_);
v___x_4555_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4547_, v___x_4554_, v_i_4551_, v___x_4544_, v___y_4548_);
lean_dec(v_i_4551_);
v___y_4528_ = v___y_4546_;
v___y_4529_ = v___y_4549_;
v___y_4530_ = v___y_4548_;
v___y_4531_ = v___y_4550_;
v___y_4532_ = v___x_4555_;
goto v___jp_4527_;
}
v___jp_4556_:
{
lean_object* v___x_4563_; 
v___x_4563_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v___y_4562_, v___x_4544_);
switch(lean_obj_tag(v___x_4563_))
{
case 0:
{
lean_object* v_index_4564_; lean_object* v_size_4565_; lean_object* v___x_4566_; 
lean_dec(v___y_4560_);
v_index_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_index_4564_);
lean_dec_ref_known(v___x_4563_, 3);
v_size_4565_ = lean_ctor_get(v___y_4562_, 0);
lean_inc(v_size_4565_);
v___x_4566_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4562_, v_size_4565_, v_index_4564_, v___x_4544_, v___y_4558_);
lean_dec(v_index_4564_);
v___y_4528_ = v___y_4557_;
v___y_4529_ = v___y_4559_;
v___y_4530_ = v___y_4558_;
v___y_4531_ = v___y_4561_;
v___y_4532_ = v___x_4566_;
goto v___jp_4527_;
}
case 1:
{
lean_object* v_index_4567_; 
lean_dec(v___y_4560_);
v_index_4567_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_index_4567_);
lean_dec_ref_known(v___x_4563_, 1);
v___y_4546_ = v___y_4557_;
v___y_4547_ = v___y_4562_;
v___y_4548_ = v___y_4558_;
v___y_4549_ = v___y_4559_;
v___y_4550_ = v___y_4561_;
v_i_4551_ = v_index_4567_;
goto v___jp_4545_;
}
default: 
{
lean_object* v___x_4568_; 
v___x_4568_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_4562_, v___y_4560_);
if (lean_obj_tag(v___x_4568_) == 0)
{
lean_object* v_index_4569_; 
v_index_4569_ = lean_ctor_get(v___x_4568_, 0);
lean_inc(v_index_4569_);
lean_dec_ref_known(v___x_4568_, 1);
v___y_4546_ = v___y_4557_;
v___y_4547_ = v___y_4562_;
v___y_4548_ = v___y_4558_;
v___y_4549_ = v___y_4559_;
v___y_4550_ = v___y_4561_;
v_i_4551_ = v_index_4569_;
goto v___jp_4545_;
}
else
{
lean_dec(v___x_4544_);
v___y_4528_ = v___y_4557_;
v___y_4529_ = v___y_4559_;
v___y_4530_ = v___y_4558_;
v___y_4531_ = v___y_4561_;
v___y_4532_ = v___y_4562_;
goto v___jp_4527_;
}
}
}
}
v___jp_4570_:
{
lean_object* v_size_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v_size_4577_ = lean_ctor_get(v___y_4572_, 0);
v___x_4578_ = lean_unsigned_to_nat(1u);
v___x_4579_ = lean_nat_add(v_size_4577_, v___x_4578_);
v___x_4580_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_4572_, v___x_4579_, v_i_4576_, v___x_4544_, v___y_4573_);
lean_dec(v_i_4576_);
v___y_4528_ = v___y_4571_;
v___y_4529_ = v___y_4574_;
v___y_4530_ = v___y_4573_;
v___y_4531_ = v___y_4575_;
v___y_4532_ = v___x_4580_;
goto v___jp_4527_;
}
v___jp_4581_:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4588_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(v___y_4587_);
lean_dec_ref(v___y_4587_);
v___x_4589_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v___x_4588_, v___x_4544_);
switch(lean_obj_tag(v___x_4589_))
{
case 0:
{
lean_object* v_index_4590_; lean_object* v_size_4591_; lean_object* v___x_4592_; 
lean_dec(v___y_4586_);
v_index_4590_ = lean_ctor_get(v___x_4589_, 0);
lean_inc(v_index_4590_);
lean_dec_ref_known(v___x_4589_, 3);
v_size_4591_ = lean_ctor_get(v___x_4588_, 0);
lean_inc(v_size_4591_);
v___x_4592_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_4588_, v_size_4591_, v_index_4590_, v___x_4544_, v___y_4584_);
lean_dec(v_index_4590_);
v___y_4528_ = v___y_4583_;
v___y_4529_ = v___y_4585_;
v___y_4530_ = v___y_4584_;
v___y_4531_ = v___y_4582_;
v___y_4532_ = v___x_4592_;
goto v___jp_4527_;
}
case 1:
{
lean_object* v_index_4593_; 
lean_dec(v___y_4586_);
v_index_4593_ = lean_ctor_get(v___x_4589_, 0);
lean_inc(v_index_4593_);
lean_dec_ref_known(v___x_4589_, 1);
v___y_4571_ = v___y_4583_;
v___y_4572_ = v___x_4588_;
v___y_4573_ = v___y_4584_;
v___y_4574_ = v___y_4585_;
v___y_4575_ = v___y_4582_;
v_i_4576_ = v_index_4593_;
goto v___jp_4570_;
}
default: 
{
lean_object* v___x_4594_; 
v___x_4594_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_4588_, v___y_4586_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_index_4595_; 
v_index_4595_ = lean_ctor_get(v___x_4594_, 0);
lean_inc(v_index_4595_);
lean_dec_ref_known(v___x_4594_, 1);
v___y_4571_ = v___y_4583_;
v___y_4572_ = v___x_4588_;
v___y_4573_ = v___y_4584_;
v___y_4574_ = v___y_4585_;
v___y_4575_ = v___y_4582_;
v_i_4576_ = v_index_4595_;
goto v___jp_4570_;
}
else
{
lean_dec(v___x_4544_);
v___y_4528_ = v___y_4583_;
v___y_4529_ = v___y_4585_;
v___y_4530_ = v___y_4584_;
v___y_4531_ = v___y_4582_;
v___y_4532_ = v___x_4588_;
goto v___jp_4527_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
lean_dec(v___x_4517_);
lean_dec_ref(v_m_4511_);
v___x_4781_ = lean_box(0);
v___x_4782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4781_);
lean_ctor_set(v___x_4782_, 1, v_a_4513_);
v___x_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4782_);
return v___x_4783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t v___x_4784_, lean_object* v_m_4785_, lean_object* v_e_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_){
_start:
{
lean_object* v___y_4792_; uint8_t v___x_4796_; 
v___x_4796_ = l_Lean_Expr_hasFVar(v_e_4786_);
if (v___x_4796_ == 0)
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
lean_dec_ref(v_m_4785_);
v___x_4797_ = lean_box(v___x_4796_);
v___x_4798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4797_);
lean_ctor_set(v___x_4798_, 1, v___y_4787_);
v___x_4799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4799_, 0, v___x_4798_);
return v___x_4799_;
}
else
{
uint8_t v___x_4800_; 
v___x_4800_ = l_Lean_Expr_isFVar(v_e_4786_);
if (v___x_4800_ == 0)
{
lean_dec_ref(v_m_4785_);
v___y_4792_ = v___y_4787_;
goto v___jp_4791_;
}
else
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = l_Lean_Expr_fvarId_x21(v_e_4786_);
v___x_4802_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_4785_, v___x_4801_, v___y_4787_, v___y_4788_, v___y_4789_);
lean_dec(v___x_4801_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v_a_4803_; lean_object* v_snd_4804_; 
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
lean_inc(v_a_4803_);
lean_dec_ref_known(v___x_4802_, 1);
v_snd_4804_ = lean_ctor_get(v_a_4803_, 1);
lean_inc(v_snd_4804_);
lean_dec(v_a_4803_);
v___y_4792_ = v_snd_4804_;
goto v___jp_4791_;
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
v_a_4805_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___x_4802_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4802_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
}
v___jp_4791_:
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4793_ = lean_box(v___x_4784_);
v___x_4794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4793_);
lean_ctor_set(v___x_4794_, 1, v___y_4792_);
v___x_4795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4794_);
return v___x_4795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object* v_m_4813_, lean_object* v_fvarId_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_4813_, v_fvarId_4814_, v_a_4815_, v_a_4816_, v_a_4817_);
lean_dec(v_a_4817_);
lean_dec_ref(v_a_4816_);
lean_dec(v_fvarId_4814_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object* v_00_u03b2_4820_, lean_object* v_m_4821_, lean_object* v_a_4822_){
_start:
{
lean_object* v___x_4823_; 
v___x_4823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_4821_, v_a_4822_);
return v___x_4823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object* v_00_u03b2_4824_, lean_object* v_m_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v_res_4827_; 
v_res_4827_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(v_00_u03b2_4824_, v_m_4825_, v_a_4826_);
lean_dec(v_a_4826_);
lean_dec_ref(v_m_4825_);
return v_res_4827_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object* v_00_u03b2_4828_, lean_object* v_m_4829_, lean_object* v_a_4830_){
_start:
{
uint8_t v___x_4831_; 
v___x_4831_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_4829_, v_a_4830_);
return v___x_4831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object* v_00_u03b2_4832_, lean_object* v_m_4833_, lean_object* v_a_4834_){
_start:
{
uint8_t v_res_4835_; lean_object* v_r_4836_; 
v_res_4835_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(v_00_u03b2_4832_, v_m_4833_, v_a_4834_);
lean_dec(v_a_4834_);
lean_dec_ref(v_m_4833_);
v_r_4836_ = lean_box(v_res_4835_);
return v_r_4836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object* v_00_u03b2_4837_, lean_object* v_m_4838_, lean_object* v_query_4839_){
_start:
{
lean_object* v___x_4840_; 
v___x_4840_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v_m_4838_, v_query_4839_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___boxed(lean_object* v_00_u03b2_4841_, lean_object* v_m_4842_, lean_object* v_query_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_00_u03b2_4841_, v_m_4842_, v_query_4843_);
lean_dec(v_query_4843_);
lean_dec_ref(v_m_4842_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object* v_00_u03b2_4845_, lean_object* v_m_4846_){
_start:
{
lean_object* v___x_4847_; 
v___x_4847_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(v_m_4846_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object* v_00_u03b2_4848_, lean_object* v_m_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_00_u03b2_4848_, v_m_4849_);
lean_dec_ref(v_m_4849_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object* v_00_u03b1_4851_, lean_object* v_msg_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_){
_start:
{
lean_object* v___x_4857_; 
v___x_4857_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___redArg(v_msg_4852_, v___y_4854_, v___y_4855_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(lean_object* v_00_u03b1_4858_, lean_object* v_msg_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_00_u03b1_4858_, v_msg_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
lean_dec_ref(v___y_4860_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object* v_00_u03b2_4865_, lean_object* v_m_4866_, lean_object* v_query_4867_){
_start:
{
lean_object* v___x_4868_; 
v___x_4868_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_m_4866_, v_query_4867_);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4869_, lean_object* v_m_4870_, lean_object* v_query_4871_){
_start:
{
lean_object* v_res_4872_; 
v_res_4872_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(v_00_u03b2_4869_, v_m_4870_, v_query_4871_);
lean_dec(v_query_4871_);
lean_dec_ref(v_m_4870_);
return v_res_4872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3(lean_object* v_00_u03b2_4873_, lean_object* v_m_4874_, lean_object* v_a_4875_){
_start:
{
lean_object* v___x_4876_; 
v___x_4876_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3___redArg(v_m_4874_, v_a_4875_);
return v___x_4876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4877_, lean_object* v_m_4878_, lean_object* v_a_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3(v_00_u03b2_4877_, v_m_4878_, v_a_4879_);
lean_dec_ref(v_a_4879_);
lean_dec_ref(v_m_4878_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(lean_object* v_00_u03b2_4881_, lean_object* v_m_4882_, lean_object* v_query_4883_){
_start:
{
lean_object* v___x_4884_; 
v___x_4884_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_m_4882_, v_query_4883_);
return v___x_4884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4885_, lean_object* v_m_4886_, lean_object* v_query_4887_){
_start:
{
lean_object* v_res_4888_; 
v_res_4888_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(v_00_u03b2_4885_, v_m_4886_, v_query_4887_);
lean_dec_ref(v_query_4887_);
lean_dec_ref(v_m_4886_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5(lean_object* v_00_u03b2_4889_, lean_object* v_m_4890_){
_start:
{
lean_object* v___x_4891_; 
v___x_4891_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5___redArg(v_m_4890_);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5___boxed(lean_object* v_00_u03b2_4892_, lean_object* v_m_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5(v_00_u03b2_4892_, v_m_4893_);
lean_dec_ref(v_m_4893_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(lean_object* v_00_u03b2_4895_, lean_object* v_m_4896_, lean_object* v_query_4897_, lean_object* v_x_4898_, lean_object* v_x_4899_, lean_object* v_x_4900_, lean_object* v_x_4901_){
_start:
{
lean_object* v___x_4902_; 
v___x_4902_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_4896_, v_query_4897_, v_x_4898_, v_x_4899_, v_x_4900_);
return v___x_4902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___boxed(lean_object* v_00_u03b2_4903_, lean_object* v_m_4904_, lean_object* v_query_4905_, lean_object* v_x_4906_, lean_object* v_x_4907_, lean_object* v_x_4908_, lean_object* v_x_4909_){
_start:
{
lean_object* v_res_4910_; 
v_res_4910_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(v_00_u03b2_4903_, v_m_4904_, v_query_4905_, v_x_4906_, v_x_4907_, v_x_4908_, v_x_4909_);
lean_dec(v_query_4905_);
lean_dec_ref(v_m_4904_);
return v_res_4910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9(lean_object* v_00_u03b2_4911_, lean_object* v_init_4912_, lean_object* v_b_4913_){
_start:
{
lean_object* v___x_4914_; 
v___x_4914_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9___redArg(v_init_4912_, v_b_4913_);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9___boxed(lean_object* v_00_u03b2_4915_, lean_object* v_init_4916_, lean_object* v_b_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9(v_00_u03b2_4915_, v_init_4916_, v_b_4917_);
lean_dec_ref(v_b_4917_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4919_, lean_object* v_m_4920_, lean_object* v_query_4921_){
_start:
{
lean_object* v___x_4922_; 
v___x_4922_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3_spec__5___redArg(v_m_4920_, v_query_4921_);
return v___x_4922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4923_, lean_object* v_m_4924_, lean_object* v_query_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__3_spec__5(v_00_u03b2_4923_, v_m_4924_, v_query_4925_);
lean_dec_ref(v_query_4925_);
lean_dec_ref(v_m_4924_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4927_, lean_object* v_m_4928_, lean_object* v_query_4929_, lean_object* v_x_4930_, lean_object* v_x_4931_, lean_object* v_x_4932_, lean_object* v_x_4933_){
_start:
{
lean_object* v___x_4934_; 
v___x_4934_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__7___redArg(v_m_4928_, v_query_4929_, v_x_4930_, v_x_4931_, v_x_4932_);
return v___x_4934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_4935_, lean_object* v_m_4936_, lean_object* v_query_4937_, lean_object* v_x_4938_, lean_object* v_x_4939_, lean_object* v_x_4940_, lean_object* v_x_4941_){
_start:
{
lean_object* v_res_4942_; 
v_res_4942_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__7(v_00_u03b2_4935_, v_m_4936_, v_query_4937_, v_x_4938_, v_x_4939_, v_x_4940_, v_x_4941_);
lean_dec_ref(v_query_4937_);
lean_dec_ref(v_m_4936_);
return v_res_4942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_4943_, lean_object* v_init_4944_, lean_object* v_b_4945_){
_start:
{
lean_object* v___x_4946_; 
v___x_4946_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9___redArg(v_init_4944_, v_b_4945_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b2_4947_, lean_object* v_init_4948_, lean_object* v_b_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9(v_00_u03b2_4947_, v_init_4948_, v_b_4949_);
lean_dec_ref(v_b_4949_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_4951_, lean_object* v_b_4952_, lean_object* v_acc_4953_, lean_object* v_i_4954_){
_start:
{
lean_object* v___x_4955_; 
v___x_4955_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9_spec__14___redArg(v_b_4952_, v_acc_4953_, v_i_4954_);
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9_spec__14___boxed(lean_object* v_00_u03b2_4956_, lean_object* v_b_4957_, lean_object* v_acc_4958_, lean_object* v_i_4959_){
_start:
{
lean_object* v_res_4960_; 
v_res_4960_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_spec__9_spec__14(v_00_u03b2_4956_, v_b_4957_, v_acc_4958_, v_i_4959_);
lean_dec_ref(v_b_4957_);
return v_res_4960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9_spec__15(lean_object* v_00_u03b2_4961_, lean_object* v_b_4962_, lean_object* v_acc_4963_, lean_object* v_i_4964_){
_start:
{
lean_object* v___x_4965_; 
v___x_4965_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9_spec__15___redArg(v_b_4962_, v_acc_4963_, v_i_4964_);
return v___x_4965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9_spec__15___boxed(lean_object* v_00_u03b2_4966_, lean_object* v_b_4967_, lean_object* v_acc_4968_, lean_object* v_i_4969_){
_start:
{
lean_object* v_res_4970_; 
v_res_4970_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__5_spec__9_spec__15(v_00_u03b2_4966_, v_b_4967_, v_acc_4968_, v_i_4969_);
lean_dec_ref(v_b_4967_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object* v_msg_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
lean_object* v___f_4976_; lean_object* v___x_10559__overap_4977_; lean_object* v___x_4978_; 
v___f_4976_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___closed__0));
v___x_10559__overap_4977_ = lean_panic_fn_borrowed(v___f_4976_, v_msg_4972_);
lean_inc(v___y_4974_);
lean_inc_ref(v___y_4973_);
v___x_4978_ = lean_apply_3(v___x_10559__overap_4977_, v___y_4973_, v___y_4974_, lean_box(0));
return v___x_4978_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___boxed(lean_object* v_msg_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v_msg_4979_, v___y_4980_, v___y_4981_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object* v_newDecls_4984_, lean_object* v_newArgs_4985_, lean_object* v_____r_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_){
_start:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4991_, 0, v_newDecls_4984_);
lean_ctor_set(v___x_4991_, 1, v_newArgs_4985_);
v___x_4992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4991_);
lean_ctor_set(v___x_4992_, 1, v___y_4987_);
v___x_4993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4992_);
return v___x_4993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object* v_newDecls_4994_, lean_object* v_newArgs_4995_, lean_object* v_____r_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_4994_, v_newArgs_4995_, v_____r_4996_, v___y_4997_, v___y_4998_, v___y_4999_);
lean_dec(v___y_4999_);
lean_dec_ref(v___y_4998_);
return v_res_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object* v_cls_5002_, lean_object* v_msg_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_){
_start:
{
lean_object* v_ref_5007_; lean_object* v___x_5008_; lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5053_; 
v_ref_5007_ = lean_ctor_get(v___y_5004_, 5);
v___x_5008_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_spec__12(v_msg_5003_, v___y_5004_, v___y_5005_);
v_a_5009_ = lean_ctor_get(v___x_5008_, 0);
v_isSharedCheck_5053_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_5011_ = v___x_5008_;
v_isShared_5012_ = v_isSharedCheck_5053_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_dec(v___x_5008_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5053_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5013_; lean_object* v_traceState_5014_; lean_object* v_env_5015_; lean_object* v_nextMacroScope_5016_; lean_object* v_ngen_5017_; lean_object* v_auxDeclNGen_5018_; lean_object* v_cache_5019_; lean_object* v_messages_5020_; lean_object* v_infoState_5021_; lean_object* v_snapshotTasks_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5052_; 
v___x_5013_ = lean_st_ref_take(v___y_5005_);
v_traceState_5014_ = lean_ctor_get(v___x_5013_, 4);
v_env_5015_ = lean_ctor_get(v___x_5013_, 0);
v_nextMacroScope_5016_ = lean_ctor_get(v___x_5013_, 1);
v_ngen_5017_ = lean_ctor_get(v___x_5013_, 2);
v_auxDeclNGen_5018_ = lean_ctor_get(v___x_5013_, 3);
v_cache_5019_ = lean_ctor_get(v___x_5013_, 5);
v_messages_5020_ = lean_ctor_get(v___x_5013_, 6);
v_infoState_5021_ = lean_ctor_get(v___x_5013_, 7);
v_snapshotTasks_5022_ = lean_ctor_get(v___x_5013_, 8);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5013_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5024_ = v___x_5013_;
v_isShared_5025_ = v_isSharedCheck_5052_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_snapshotTasks_5022_);
lean_inc(v_infoState_5021_);
lean_inc(v_messages_5020_);
lean_inc(v_cache_5019_);
lean_inc(v_traceState_5014_);
lean_inc(v_auxDeclNGen_5018_);
lean_inc(v_ngen_5017_);
lean_inc(v_nextMacroScope_5016_);
lean_inc(v_env_5015_);
lean_dec(v___x_5013_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5052_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
uint64_t v_tid_5026_; lean_object* v_traces_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5051_; 
v_tid_5026_ = lean_ctor_get_uint64(v_traceState_5014_, sizeof(void*)*1);
v_traces_5027_ = lean_ctor_get(v_traceState_5014_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v_traceState_5014_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5029_ = v_traceState_5014_;
v_isShared_5030_ = v_isSharedCheck_5051_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_traces_5027_);
lean_dec(v_traceState_5014_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5051_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v___x_5031_; double v___x_5032_; uint8_t v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5041_; 
v___x_5031_ = lean_box(0);
v___x_5032_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__0);
v___x_5033_ = 0;
v___x_5034_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__1));
v___x_5035_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5035_, 0, v_cls_5002_);
lean_ctor_set(v___x_5035_, 1, v___x_5031_);
lean_ctor_set(v___x_5035_, 2, v___x_5034_);
lean_ctor_set_float(v___x_5035_, sizeof(void*)*3, v___x_5032_);
lean_ctor_set_float(v___x_5035_, sizeof(void*)*3 + 8, v___x_5032_);
lean_ctor_set_uint8(v___x_5035_, sizeof(void*)*3 + 16, v___x_5033_);
v___x_5036_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7___closed__2));
v___x_5037_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5035_);
lean_ctor_set(v___x_5037_, 1, v_a_5009_);
lean_ctor_set(v___x_5037_, 2, v___x_5036_);
lean_inc(v_ref_5007_);
v___x_5038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5038_, 0, v_ref_5007_);
lean_ctor_set(v___x_5038_, 1, v___x_5037_);
v___x_5039_ = l_Lean_PersistentArray_push___redArg(v_traces_5027_, v___x_5038_);
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 0, v___x_5039_);
v___x_5041_ = v___x_5029_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v___x_5039_);
lean_ctor_set_uint64(v_reuseFailAlloc_5050_, sizeof(void*)*1, v_tid_5026_);
v___x_5041_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
lean_object* v___x_5043_; 
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 4, v___x_5041_);
v___x_5043_ = v___x_5024_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_env_5015_);
lean_ctor_set(v_reuseFailAlloc_5049_, 1, v_nextMacroScope_5016_);
lean_ctor_set(v_reuseFailAlloc_5049_, 2, v_ngen_5017_);
lean_ctor_set(v_reuseFailAlloc_5049_, 3, v_auxDeclNGen_5018_);
lean_ctor_set(v_reuseFailAlloc_5049_, 4, v___x_5041_);
lean_ctor_set(v_reuseFailAlloc_5049_, 5, v_cache_5019_);
lean_ctor_set(v_reuseFailAlloc_5049_, 6, v_messages_5020_);
lean_ctor_set(v_reuseFailAlloc_5049_, 7, v_infoState_5021_);
lean_ctor_set(v_reuseFailAlloc_5049_, 8, v_snapshotTasks_5022_);
v___x_5043_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5047_; 
v___x_5044_ = lean_st_ref_put(v___y_5005_, v___x_5043_);
v___x_5045_ = lean_box(0);
if (v_isShared_5012_ == 0)
{
lean_ctor_set(v___x_5011_, 0, v___x_5045_);
v___x_5047_ = v___x_5011_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5045_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
return v___x_5047_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5___boxed(lean_object* v_cls_5054_, lean_object* v_msg_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_){
_start:
{
lean_object* v_res_5059_; 
v_res_5059_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v_cls_5054_, v_msg_5055_, v___y_5056_, v___y_5057_);
lean_dec(v___y_5057_);
lean_dec_ref(v___y_5056_);
return v_res_5059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(size_t v_sz_5060_, size_t v_i_5061_, lean_object* v_bs_5062_){
_start:
{
uint8_t v___x_5063_; 
v___x_5063_ = lean_usize_dec_lt(v_i_5061_, v_sz_5060_);
if (v___x_5063_ == 0)
{
return v_bs_5062_;
}
else
{
lean_object* v_v_5064_; lean_object* v___x_5065_; lean_object* v_bs_x27_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; size_t v___x_5069_; size_t v___x_5070_; lean_object* v___x_5071_; 
v_v_5064_ = lean_array_uget(v_bs_5062_, v_i_5061_);
v___x_5065_ = lean_unsigned_to_nat(0u);
v_bs_x27_5066_ = lean_array_uset(v_bs_5062_, v_i_5061_, v___x_5065_);
v___x_5067_ = l_Lean_LocalDecl_fvarId(v_v_5064_);
lean_dec(v_v_5064_);
v___x_5068_ = l_Lean_mkFVar(v___x_5067_);
v___x_5069_ = ((size_t)1ULL);
v___x_5070_ = lean_usize_add(v_i_5061_, v___x_5069_);
v___x_5071_ = lean_array_uset(v_bs_x27_5066_, v_i_5061_, v___x_5068_);
v_i_5061_ = v___x_5070_;
v_bs_5062_ = v___x_5071_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object* v_sz_5073_, lean_object* v_i_5074_, lean_object* v_bs_5075_){
_start:
{
size_t v_sz_boxed_5076_; size_t v_i_boxed_5077_; lean_object* v_res_5078_; 
v_sz_boxed_5076_ = lean_unbox_usize(v_sz_5073_);
lean_dec(v_sz_5073_);
v_i_boxed_5077_ = lean_unbox_usize(v_i_5074_);
lean_dec(v_i_5074_);
v_res_5078_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_sz_boxed_5076_, v_i_boxed_5077_, v_bs_5075_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(lean_object* v_as_5079_, size_t v_sz_5080_, size_t v_i_5081_, lean_object* v_b_5082_){
_start:
{
uint8_t v___x_5084_; 
v___x_5084_ = lean_usize_dec_lt(v_i_5081_, v_sz_5080_);
if (v___x_5084_ == 0)
{
lean_object* v___x_5085_; 
v___x_5085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5085_, 0, v_b_5082_);
return v___x_5085_;
}
else
{
lean_object* v_snd_5086_; lean_object* v_fst_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5183_; 
v_snd_5086_ = lean_ctor_get(v_b_5082_, 1);
v_fst_5087_ = lean_ctor_get(v_b_5082_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v_b_5082_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5089_ = v_b_5082_;
v_isShared_5090_ = v_isSharedCheck_5183_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_snd_5086_);
lean_inc(v_fst_5087_);
lean_dec(v_b_5082_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5183_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v_array_5091_; lean_object* v_start_5092_; lean_object* v_stop_5093_; uint8_t v___x_5094_; 
v_array_5091_ = lean_ctor_get(v_snd_5086_, 0);
v_start_5092_ = lean_ctor_get(v_snd_5086_, 1);
v_stop_5093_ = lean_ctor_get(v_snd_5086_, 2);
v___x_5094_ = lean_nat_dec_lt(v_start_5092_, v_stop_5093_);
if (v___x_5094_ == 0)
{
lean_object* v___x_5096_; 
if (v_isShared_5090_ == 0)
{
v___x_5096_ = v___x_5089_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_fst_5087_);
lean_ctor_set(v_reuseFailAlloc_5098_, 1, v_snd_5086_);
v___x_5096_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
lean_object* v___x_5097_; 
v___x_5097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5097_, 0, v___x_5096_);
return v___x_5097_;
}
}
else
{
lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5179_; 
lean_inc(v_stop_5093_);
lean_inc(v_start_5092_);
lean_inc_ref(v_array_5091_);
v_isSharedCheck_5179_ = !lean_is_exclusive(v_snd_5086_);
if (v_isSharedCheck_5179_ == 0)
{
lean_object* v_unused_5180_; lean_object* v_unused_5181_; lean_object* v_unused_5182_; 
v_unused_5180_ = lean_ctor_get(v_snd_5086_, 2);
lean_dec(v_unused_5180_);
v_unused_5181_ = lean_ctor_get(v_snd_5086_, 1);
lean_dec(v_unused_5181_);
v_unused_5182_ = lean_ctor_get(v_snd_5086_, 0);
lean_dec(v_unused_5182_);
v___x_5100_ = v_snd_5086_;
v_isShared_5101_ = v_isSharedCheck_5179_;
goto v_resetjp_5099_;
}
else
{
lean_dec(v_snd_5086_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5179_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
lean_object* v_a_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5107_; 
v_a_5102_ = lean_array_uget_borrowed(v_as_5079_, v_i_5081_);
v___x_5103_ = lean_array_fget(v_array_5091_, v_start_5092_);
v___x_5104_ = lean_unsigned_to_nat(1u);
v___x_5105_ = lean_nat_add(v_start_5092_, v___x_5104_);
lean_dec(v_start_5092_);
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 1, v___x_5105_);
v___x_5107_ = v___x_5100_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_array_5091_);
lean_ctor_set(v_reuseFailAlloc_5178_, 1, v___x_5105_);
lean_ctor_set(v_reuseFailAlloc_5178_, 2, v_stop_5093_);
v___x_5107_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
lean_object* v___y_5109_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___y_5119_; lean_object* v_i_5120_; lean_object* v___y_5125_; lean_object* v___y_5135_; lean_object* v_i_5136_; lean_object* v___x_5150_; 
v___x_5116_ = l_Lean_LocalDecl_fvarId(v_a_5102_);
lean_inc(v_a_5102_);
v___x_5117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5117_, 0, v_a_5102_);
lean_ctor_set(v___x_5117_, 1, v___x_5103_);
v___x_5150_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v_fst_5087_, v___x_5116_);
switch(lean_obj_tag(v___x_5150_))
{
case 0:
{
lean_object* v_index_5151_; lean_object* v_size_5152_; lean_object* v___x_5153_; 
v_index_5151_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_index_5151_);
lean_dec_ref_known(v___x_5150_, 3);
v_size_5152_ = lean_ctor_get(v_fst_5087_, 0);
lean_inc(v_size_5152_);
v___x_5153_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_5087_, v_size_5152_, v_index_5151_, v___x_5116_, v___x_5117_);
lean_dec(v_index_5151_);
v___y_5109_ = v___x_5153_;
goto v___jp_5108_;
}
case 1:
{
lean_object* v_index_5154_; lean_object* v_size_5155_; lean_object* v_keyArray_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; uint8_t v___x_5159_; 
v_index_5154_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_index_5154_);
lean_dec_ref_known(v___x_5150_, 1);
v_size_5155_ = lean_ctor_get(v_fst_5087_, 0);
v_keyArray_5156_ = lean_ctor_get(v_fst_5087_, 1);
v___x_5157_ = lean_nat_add(v_size_5155_, v___x_5104_);
v___x_5158_ = lean_array_get_size(v_keyArray_5156_);
v___x_5159_ = lean_nat_dec_lt(v___x_5157_, v___x_5158_);
if (v___x_5159_ == 0)
{
lean_dec(v___x_5157_);
lean_dec(v_index_5154_);
goto v___jp_5140_;
}
else
{
lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; uint8_t v___x_5164_; 
v___x_5160_ = lean_unsigned_to_nat(4u);
v___x_5161_ = lean_nat_mul(v___x_5157_, v___x_5160_);
v___x_5162_ = lean_unsigned_to_nat(3u);
v___x_5163_ = lean_nat_mul(v___x_5158_, v___x_5162_);
v___x_5164_ = lean_nat_dec_le(v___x_5161_, v___x_5163_);
lean_dec(v___x_5163_);
lean_dec(v___x_5161_);
if (v___x_5164_ == 0)
{
lean_dec(v___x_5157_);
lean_dec(v_index_5154_);
goto v___jp_5140_;
}
else
{
lean_object* v___x_5165_; 
v___x_5165_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_5087_, v___x_5157_, v_index_5154_, v___x_5116_, v___x_5117_);
lean_dec(v_index_5154_);
v___y_5109_ = v___x_5165_;
goto v___jp_5108_;
}
}
}
default: 
{
lean_object* v_size_5166_; lean_object* v_keyArray_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; uint8_t v___x_5170_; 
v_size_5166_ = lean_ctor_get(v_fst_5087_, 0);
v_keyArray_5167_ = lean_ctor_get(v_fst_5087_, 1);
v___x_5168_ = lean_nat_add(v_size_5166_, v___x_5104_);
v___x_5169_ = lean_array_get_size(v_keyArray_5167_);
v___x_5170_ = lean_nat_dec_lt(v___x_5168_, v___x_5169_);
if (v___x_5170_ == 0)
{
lean_object* v___x_5171_; 
lean_dec(v___x_5168_);
v___x_5171_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(v_fst_5087_);
lean_dec(v_fst_5087_);
v___y_5125_ = v___x_5171_;
goto v___jp_5124_;
}
else
{
lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; uint8_t v___x_5176_; 
v___x_5172_ = lean_unsigned_to_nat(4u);
v___x_5173_ = lean_nat_mul(v___x_5168_, v___x_5172_);
lean_dec(v___x_5168_);
v___x_5174_ = lean_unsigned_to_nat(3u);
v___x_5175_ = lean_nat_mul(v___x_5169_, v___x_5174_);
v___x_5176_ = lean_nat_dec_le(v___x_5173_, v___x_5175_);
lean_dec(v___x_5175_);
lean_dec(v___x_5173_);
if (v___x_5176_ == 0)
{
lean_object* v___x_5177_; 
v___x_5177_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(v_fst_5087_);
lean_dec(v_fst_5087_);
v___y_5125_ = v___x_5177_;
goto v___jp_5124_;
}
else
{
v___y_5125_ = v_fst_5087_;
goto v___jp_5124_;
}
}
}
}
v___jp_5108_:
{
lean_object* v___x_5111_; 
if (v_isShared_5090_ == 0)
{
lean_ctor_set(v___x_5089_, 1, v___x_5107_);
lean_ctor_set(v___x_5089_, 0, v___y_5109_);
v___x_5111_ = v___x_5089_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v___y_5109_);
lean_ctor_set(v_reuseFailAlloc_5115_, 1, v___x_5107_);
v___x_5111_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
size_t v___x_5112_; size_t v___x_5113_; 
v___x_5112_ = ((size_t)1ULL);
v___x_5113_ = lean_usize_add(v_i_5081_, v___x_5112_);
v_i_5081_ = v___x_5113_;
v_b_5082_ = v___x_5111_;
goto _start;
}
}
v___jp_5118_:
{
lean_object* v_size_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; 
v_size_5121_ = lean_ctor_get(v___y_5119_, 0);
v___x_5122_ = lean_nat_add(v_size_5121_, v___x_5104_);
v___x_5123_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_5119_, v___x_5122_, v_i_5120_, v___x_5116_, v___x_5117_);
lean_dec(v_i_5120_);
v___y_5109_ = v___x_5123_;
goto v___jp_5108_;
}
v___jp_5124_:
{
lean_object* v___x_5126_; 
v___x_5126_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v___y_5125_, v___x_5116_);
switch(lean_obj_tag(v___x_5126_))
{
case 0:
{
lean_object* v_index_5127_; lean_object* v_size_5128_; lean_object* v___x_5129_; 
v_index_5127_ = lean_ctor_get(v___x_5126_, 0);
lean_inc(v_index_5127_);
lean_dec_ref_known(v___x_5126_, 3);
v_size_5128_ = lean_ctor_get(v___y_5125_, 0);
lean_inc(v_size_5128_);
v___x_5129_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_5125_, v_size_5128_, v_index_5127_, v___x_5116_, v___x_5117_);
lean_dec(v_index_5127_);
v___y_5109_ = v___x_5129_;
goto v___jp_5108_;
}
case 1:
{
lean_object* v_index_5130_; 
v_index_5130_ = lean_ctor_get(v___x_5126_, 0);
lean_inc(v_index_5130_);
lean_dec_ref_known(v___x_5126_, 1);
v___y_5119_ = v___y_5125_;
v_i_5120_ = v_index_5130_;
goto v___jp_5118_;
}
default: 
{
lean_object* v___x_5131_; lean_object* v___x_5132_; 
v___x_5131_ = lean_unsigned_to_nat(0u);
v___x_5132_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_5125_, v___x_5131_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v_index_5133_; 
v_index_5133_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_index_5133_);
lean_dec_ref_known(v___x_5132_, 1);
v___y_5119_ = v___y_5125_;
v_i_5120_ = v_index_5133_;
goto v___jp_5118_;
}
else
{
lean_dec_ref_known(v___x_5117_, 2);
lean_dec(v___x_5116_);
v___y_5109_ = v___y_5125_;
goto v___jp_5108_;
}
}
}
}
v___jp_5134_:
{
lean_object* v_size_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; 
v_size_5137_ = lean_ctor_get(v___y_5135_, 0);
v___x_5138_ = lean_nat_add(v_size_5137_, v___x_5104_);
v___x_5139_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_5135_, v___x_5138_, v_i_5136_, v___x_5116_, v___x_5117_);
lean_dec(v_i_5136_);
v___y_5109_ = v___x_5139_;
goto v___jp_5108_;
}
v___jp_5140_:
{
lean_object* v___x_5141_; lean_object* v___x_5142_; 
v___x_5141_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___redArg(v_fst_5087_);
lean_dec(v_fst_5087_);
v___x_5142_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___redArg(v___x_5141_, v___x_5116_);
switch(lean_obj_tag(v___x_5142_))
{
case 0:
{
lean_object* v_index_5143_; lean_object* v_size_5144_; lean_object* v___x_5145_; 
v_index_5143_ = lean_ctor_get(v___x_5142_, 0);
lean_inc(v_index_5143_);
lean_dec_ref_known(v___x_5142_, 3);
v_size_5144_ = lean_ctor_get(v___x_5141_, 0);
lean_inc(v_size_5144_);
v___x_5145_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_5141_, v_size_5144_, v_index_5143_, v___x_5116_, v___x_5117_);
lean_dec(v_index_5143_);
v___y_5109_ = v___x_5145_;
goto v___jp_5108_;
}
case 1:
{
lean_object* v_index_5146_; 
v_index_5146_ = lean_ctor_get(v___x_5142_, 0);
lean_inc(v_index_5146_);
lean_dec_ref_known(v___x_5142_, 1);
v___y_5135_ = v___x_5141_;
v_i_5136_ = v_index_5146_;
goto v___jp_5134_;
}
default: 
{
lean_object* v___x_5147_; lean_object* v___x_5148_; 
v___x_5147_ = lean_unsigned_to_nat(0u);
v___x_5148_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_5141_, v___x_5147_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_object* v_index_5149_; 
v_index_5149_ = lean_ctor_get(v___x_5148_, 0);
lean_inc(v_index_5149_);
lean_dec_ref_known(v___x_5148_, 1);
v___y_5135_ = v___x_5141_;
v_i_5136_ = v_index_5149_;
goto v___jp_5134_;
}
else
{
lean_dec_ref_known(v___x_5117_, 2);
lean_dec(v___x_5116_);
v___y_5109_ = v___x_5141_;
goto v___jp_5108_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg___boxed(lean_object* v_as_5184_, lean_object* v_sz_5185_, lean_object* v_i_5186_, lean_object* v_b_5187_, lean_object* v___y_5188_){
_start:
{
size_t v_sz_boxed_5189_; size_t v_i_boxed_5190_; lean_object* v_res_5191_; 
v_sz_boxed_5189_ = lean_unbox_usize(v_sz_5185_);
lean_dec(v_sz_5185_);
v_i_boxed_5190_ = lean_unbox_usize(v_i_5186_);
lean_dec(v_i_5186_);
v_res_5191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_as_5184_, v_sz_boxed_5189_, v_i_boxed_5190_, v_b_5187_);
lean_dec_ref(v_as_5184_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(lean_object* v_a_5192_, lean_object* v_a_5193_){
_start:
{
if (lean_obj_tag(v_a_5192_) == 0)
{
lean_object* v___x_5194_; 
v___x_5194_ = l_List_reverse___redArg(v_a_5193_);
return v___x_5194_;
}
else
{
lean_object* v_head_5195_; lean_object* v_tail_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5205_; 
v_head_5195_ = lean_ctor_get(v_a_5192_, 0);
v_tail_5196_ = lean_ctor_get(v_a_5192_, 1);
v_isSharedCheck_5205_ = !lean_is_exclusive(v_a_5192_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5198_ = v_a_5192_;
v_isShared_5199_ = v_isSharedCheck_5205_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_tail_5196_);
lean_inc(v_head_5195_);
lean_dec(v_a_5192_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5205_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5200_; lean_object* v___x_5202_; 
v___x_5200_ = l_Lean_MessageData_ofExpr(v_head_5195_);
if (v_isShared_5199_ == 0)
{
lean_ctor_set(v___x_5198_, 1, v_a_5193_);
lean_ctor_set(v___x_5198_, 0, v___x_5200_);
v___x_5202_ = v___x_5198_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v___x_5200_);
lean_ctor_set(v_reuseFailAlloc_5204_, 1, v_a_5193_);
v___x_5202_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
v_a_5192_ = v_tail_5196_;
v_a_5193_ = v___x_5202_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object* v___x_5206_, lean_object* v_as_5207_, size_t v_sz_5208_, size_t v_i_5209_, lean_object* v_b_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_){
_start:
{
uint8_t v___x_5215_; 
v___x_5215_ = lean_usize_dec_lt(v_i_5209_, v_sz_5208_);
if (v___x_5215_ == 0)
{
lean_object* v___x_5216_; lean_object* v___x_5217_; 
lean_dec_ref(v___x_5206_);
v___x_5216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5216_, 0, v_b_5210_);
lean_ctor_set(v___x_5216_, 1, v___y_5211_);
v___x_5217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5217_, 0, v___x_5216_);
return v___x_5217_;
}
else
{
lean_object* v_a_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; 
v_a_5218_ = lean_array_uget_borrowed(v_as_5207_, v_i_5209_);
v___x_5219_ = l_Lean_LocalDecl_fvarId(v_a_5218_);
lean_inc_ref(v___x_5206_);
v___x_5220_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v___x_5206_, v___x_5219_, v___y_5211_, v___y_5212_, v___y_5213_);
lean_dec(v___x_5219_);
if (lean_obj_tag(v___x_5220_) == 0)
{
lean_object* v_a_5221_; lean_object* v_snd_5222_; lean_object* v___x_5223_; size_t v___x_5224_; size_t v___x_5225_; 
v_a_5221_ = lean_ctor_get(v___x_5220_, 0);
lean_inc(v_a_5221_);
lean_dec_ref_known(v___x_5220_, 1);
v_snd_5222_ = lean_ctor_get(v_a_5221_, 1);
lean_inc(v_snd_5222_);
lean_dec(v_a_5221_);
v___x_5223_ = lean_box(0);
v___x_5224_ = ((size_t)1ULL);
v___x_5225_ = lean_usize_add(v_i_5209_, v___x_5224_);
v_i_5209_ = v___x_5225_;
v_b_5210_ = v___x_5223_;
v___y_5211_ = v_snd_5222_;
goto _start;
}
else
{
lean_dec_ref(v___x_5206_);
return v___x_5220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object* v___x_5227_, lean_object* v_as_5228_, lean_object* v_sz_5229_, lean_object* v_i_5230_, lean_object* v_b_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_){
_start:
{
size_t v_sz_boxed_5236_; size_t v_i_boxed_5237_; lean_object* v_res_5238_; 
v_sz_boxed_5236_ = lean_unbox_usize(v_sz_5229_);
lean_dec(v_sz_5229_);
v_i_boxed_5237_ = lean_unbox_usize(v_i_5230_);
lean_dec(v_i_5230_);
v_res_5238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v___x_5227_, v_as_5228_, v_sz_boxed_5236_, v_i_boxed_5237_, v_b_5231_, v___y_5232_, v___y_5233_, v___y_5234_);
lean_dec(v___y_5234_);
lean_dec_ref(v___y_5233_);
lean_dec_ref(v_as_5228_);
return v_res_5238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2(void){
_start:
{
lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5241_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1));
v___x_5242_ = lean_unsigned_to_nat(2u);
v___x_5243_ = lean_unsigned_to_nat(366u);
v___x_5244_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_5245_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3));
v___x_5246_ = l_mkPanicMessageWithDecl(v___x_5245_, v___x_5244_, v___x_5243_, v___x_5242_, v___x_5241_);
return v___x_5246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4(void){
_start:
{
lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; 
v___x_5248_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3));
v___x_5249_ = lean_unsigned_to_nat(2u);
v___x_5250_ = lean_unsigned_to_nat(367u);
v___x_5251_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_5252_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3));
v___x_5253_ = l_mkPanicMessageWithDecl(v___x_5252_, v___x_5251_, v___x_5250_, v___x_5249_, v___x_5248_);
return v___x_5253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5(void){
_start:
{
lean_object* v_cellCount_5254_; lean_object* v___x_5255_; 
v_cellCount_5254_ = lean_unsigned_to_nat(16u);
v___x_5255_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_5254_);
return v___x_5255_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6(void){
_start:
{
lean_object* v_cellCount_5256_; lean_object* v___x_5257_; 
v_cellCount_5256_ = lean_unsigned_to_nat(16u);
v___x_5257_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_5256_);
return v___x_5257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7(void){
_start:
{
lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; 
v___x_5258_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6);
v___x_5259_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5);
v___x_5260_ = lean_unsigned_to_nat(0u);
v___x_5261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5260_);
lean_ctor_set(v___x_5261_, 1, v___x_5259_);
lean_ctor_set(v___x_5261_, 2, v___x_5258_);
return v___x_5261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9(void){
_start:
{
lean_object* v___x_5263_; lean_object* v___x_5264_; 
v___x_5263_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8));
v___x_5264_ = l_Lean_stringToMessageData(v___x_5263_);
return v___x_5264_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__11(void){
_start:
{
lean_object* v___x_5266_; lean_object* v___x_5267_; 
v___x_5266_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10));
v___x_5267_ = l_Lean_stringToMessageData(v___x_5266_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object* v_sortedDecls_5268_, lean_object* v_sortedArgs_5269_, lean_object* v_toSortDecls_5270_, lean_object* v_toSortArgs_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_){
_start:
{
lean_object* v___y_5276_; lean_object* v___y_5295_; lean_object* v___y_5296_; lean_object* v___y_5297_; lean_object* v___y_5298_; lean_object* v_snd_5299_; lean_object* v___x_5301_; lean_object* v___x_5302_; uint8_t v___x_5303_; 
v___x_5301_ = lean_array_get_size(v_sortedDecls_5268_);
v___x_5302_ = lean_array_get_size(v_sortedArgs_5269_);
v___x_5303_ = lean_nat_dec_eq(v___x_5301_, v___x_5302_);
if (v___x_5303_ == 0)
{
lean_object* v___x_5304_; lean_object* v___x_5305_; 
lean_dec_ref(v_toSortArgs_5271_);
lean_dec_ref(v_sortedArgs_5269_);
lean_dec_ref(v_sortedDecls_5268_);
v___x_5304_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2);
v___x_5305_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v___x_5304_, v_a_5272_, v_a_5273_);
return v___x_5305_;
}
else
{
lean_object* v___x_5306_; lean_object* v___x_5307_; uint8_t v___x_5308_; 
v___x_5306_ = lean_array_get_size(v_toSortDecls_5270_);
v___x_5307_ = lean_array_get_size(v_toSortArgs_5271_);
v___x_5308_ = lean_nat_dec_eq(v___x_5306_, v___x_5307_);
if (v___x_5308_ == 0)
{
lean_object* v___x_5309_; lean_object* v___x_5310_; 
lean_dec_ref(v_toSortArgs_5271_);
lean_dec_ref(v_sortedArgs_5269_);
lean_dec_ref(v_sortedDecls_5268_);
v___x_5309_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4);
v___x_5310_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(v___x_5309_, v_a_5272_, v_a_5273_);
return v___x_5310_;
}
else
{
lean_object* v___x_5311_; uint8_t v___x_5312_; 
v___x_5311_ = lean_unsigned_to_nat(0u);
v___x_5312_ = lean_nat_dec_eq(v___x_5306_, v___x_5311_);
if (v___x_5312_ == 0)
{
lean_object* v_options_5313_; lean_object* v_inheritedTraceOptions_5314_; uint8_t v_hasTrace_5315_; lean_object* v_cls_5316_; lean_object* v___y_5318_; lean_object* v___y_5319_; 
v_options_5313_ = lean_ctor_get(v_a_5272_, 2);
v_inheritedTraceOptions_5314_ = lean_ctor_get(v_a_5272_, 13);
v_hasTrace_5315_ = lean_ctor_get_uint8(v_options_5313_, sizeof(void*)*1);
v_cls_5316_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11));
if (v_hasTrace_5315_ == 0)
{
v___y_5318_ = v_a_5272_;
v___y_5319_ = v_a_5273_;
goto v___jp_5317_;
}
else
{
lean_object* v___x_5420_; uint8_t v___x_5421_; 
v___x_5420_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14);
v___x_5421_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5314_, v_options_5313_, v___x_5420_);
if (v___x_5421_ == 0)
{
v___y_5318_ = v_a_5272_;
v___y_5319_ = v_a_5273_;
goto v___jp_5317_;
}
else
{
lean_object* v___x_5422_; lean_object* v___x_5423_; 
v___x_5422_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__11, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__11_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__11);
v___x_5423_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v_cls_5316_, v___x_5422_, v_a_5272_, v_a_5273_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_dec_ref_known(v___x_5423_, 1);
v___y_5318_ = v_a_5272_;
v___y_5319_ = v_a_5273_;
goto v___jp_5317_;
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
lean_dec_ref(v_toSortArgs_5271_);
lean_dec_ref(v_sortedArgs_5269_);
lean_dec_ref(v_sortedDecls_5268_);
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___x_5423_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5423_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
v___x_5429_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
return v___x_5429_;
}
}
}
}
}
v___jp_5317_:
{
lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; size_t v_sz_5323_; size_t v___x_5324_; lean_object* v___x_5325_; 
v___x_5320_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7);
v___x_5321_ = l_Array_toSubarray___redArg(v_sortedArgs_5269_, v___x_5311_, v___x_5302_);
v___x_5322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5322_, 0, v___x_5320_);
lean_ctor_set(v___x_5322_, 1, v___x_5321_);
v_sz_5323_ = lean_array_size(v_sortedDecls_5268_);
v___x_5324_ = ((size_t)0ULL);
v___x_5325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_sortedDecls_5268_, v_sz_5323_, v___x_5324_, v___x_5322_);
if (lean_obj_tag(v___x_5325_) == 0)
{
lean_object* v_a_5326_; lean_object* v_fst_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5410_; 
v_a_5326_ = lean_ctor_get(v___x_5325_, 0);
lean_inc(v_a_5326_);
lean_dec_ref_known(v___x_5325_, 1);
v_fst_5327_ = lean_ctor_get(v_a_5326_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v_a_5326_);
if (v_isSharedCheck_5410_ == 0)
{
lean_object* v_unused_5411_; 
v_unused_5411_ = lean_ctor_get(v_a_5326_, 1);
lean_dec(v_unused_5411_);
v___x_5329_ = v_a_5326_;
v_isShared_5330_ = v_isSharedCheck_5410_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_fst_5327_);
lean_dec(v_a_5326_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5410_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5331_; lean_object* v___x_5333_; 
v___x_5331_ = l_Array_toSubarray___redArg(v_toSortArgs_5271_, v___x_5311_, v___x_5307_);
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 1, v___x_5331_);
v___x_5333_ = v___x_5329_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_fst_5327_);
lean_ctor_set(v_reuseFailAlloc_5409_, 1, v___x_5331_);
v___x_5333_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
size_t v_sz_5334_; lean_object* v___x_5335_; 
v_sz_5334_ = lean_array_size(v_toSortDecls_5270_);
v___x_5335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_toSortDecls_5270_, v_sz_5334_, v___x_5324_, v___x_5333_);
if (lean_obj_tag(v___x_5335_) == 0)
{
lean_object* v_a_5336_; lean_object* v_fst_5337_; lean_object* v_size_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; 
v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
lean_inc(v_a_5336_);
lean_dec_ref_known(v___x_5335_, 1);
v_fst_5337_ = lean_ctor_get(v_a_5336_, 0);
lean_inc_n(v_fst_5337_, 2);
lean_dec(v_a_5336_);
v_size_5338_ = lean_ctor_get(v_fst_5337_, 0);
v___x_5339_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_5340_ = lean_mk_empty_array_with_capacity(v_size_5338_);
lean_inc_ref(v___x_5340_);
v___x_5341_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5339_);
lean_ctor_set(v___x_5341_, 1, v___x_5339_);
lean_ctor_set(v___x_5341_, 2, v___x_5340_);
lean_ctor_set(v___x_5341_, 3, v___x_5340_);
v___x_5342_ = lean_box(0);
v___x_5343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_fst_5337_, v_sortedDecls_5268_, v_sz_5323_, v___x_5324_, v___x_5342_, v___x_5341_, v___y_5318_, v___y_5319_);
lean_dec_ref(v_sortedDecls_5268_);
if (lean_obj_tag(v___x_5343_) == 0)
{
lean_object* v_a_5344_; lean_object* v_snd_5345_; lean_object* v___x_5346_; 
v_a_5344_ = lean_ctor_get(v___x_5343_, 0);
lean_inc(v_a_5344_);
lean_dec_ref_known(v___x_5343_, 1);
v_snd_5345_ = lean_ctor_get(v_a_5344_, 1);
lean_inc(v_snd_5345_);
lean_dec(v_a_5344_);
v___x_5346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_fst_5337_, v_toSortDecls_5270_, v_sz_5334_, v___x_5324_, v___x_5342_, v_snd_5345_, v___y_5318_, v___y_5319_);
if (lean_obj_tag(v___x_5346_) == 0)
{
lean_object* v_a_5347_; lean_object* v_snd_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5383_; 
v_a_5347_ = lean_ctor_get(v___x_5346_, 0);
lean_inc(v_a_5347_);
lean_dec_ref_known(v___x_5346_, 1);
v_snd_5348_ = lean_ctor_get(v_a_5347_, 1);
v_isSharedCheck_5383_ = !lean_is_exclusive(v_a_5347_);
if (v_isSharedCheck_5383_ == 0)
{
lean_object* v_unused_5384_; 
v_unused_5384_ = lean_ctor_get(v_a_5347_, 0);
lean_dec(v_unused_5384_);
v___x_5350_ = v_a_5347_;
v_isShared_5351_ = v_isSharedCheck_5383_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_snd_5348_);
lean_dec(v_a_5347_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5383_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v_options_5352_; lean_object* v_newDecls_5353_; lean_object* v_newArgs_5354_; lean_object* v_inheritedTraceOptions_5355_; uint8_t v_hasTrace_5356_; lean_object* v___f_5357_; 
v_options_5352_ = lean_ctor_get(v___y_5318_, 2);
v_newDecls_5353_ = lean_ctor_get(v_snd_5348_, 2);
v_newArgs_5354_ = lean_ctor_get(v_snd_5348_, 3);
v_inheritedTraceOptions_5355_ = lean_ctor_get(v___y_5318_, 13);
v_hasTrace_5356_ = lean_ctor_get_uint8(v_options_5352_, sizeof(void*)*1);
lean_inc_ref(v_newArgs_5354_);
lean_inc_ref(v_newDecls_5353_);
v___f_5357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed), 7, 2);
lean_closure_set(v___f_5357_, 0, v_newDecls_5353_);
lean_closure_set(v___f_5357_, 1, v_newArgs_5354_);
if (v_hasTrace_5356_ == 0)
{
lean_del_object(v___x_5350_);
v___y_5295_ = v___y_5319_;
v___y_5296_ = v___x_5342_;
v___y_5297_ = v___f_5357_;
v___y_5298_ = v___y_5318_;
v_snd_5299_ = v_snd_5348_;
goto v___jp_5294_;
}
else
{
lean_object* v___x_5358_; uint8_t v___x_5359_; 
v___x_5358_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14);
v___x_5359_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5355_, v_options_5352_, v___x_5358_);
if (v___x_5359_ == 0)
{
lean_del_object(v___x_5350_);
v___y_5295_ = v___y_5319_;
v___y_5296_ = v___x_5342_;
v___y_5297_ = v___f_5357_;
v___y_5298_ = v___y_5318_;
v_snd_5299_ = v_snd_5348_;
goto v___jp_5294_;
}
else
{
lean_object* v___x_5360_; size_t v_sz_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5368_; 
lean_inc_ref(v_newArgs_5354_);
lean_inc_ref_n(v_newDecls_5353_, 2);
lean_dec_ref(v___f_5357_);
v___x_5360_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9);
v_sz_5361_ = lean_array_size(v_newDecls_5353_);
v___x_5362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_sz_5361_, v___x_5324_, v_newDecls_5353_);
v___x_5363_ = lean_array_to_list(v___x_5362_);
v___x_5364_ = lean_box(0);
v___x_5365_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v___x_5363_, v___x_5364_);
v___x_5366_ = l_Lean_MessageData_ofList(v___x_5365_);
if (v_isShared_5351_ == 0)
{
lean_ctor_set_tag(v___x_5350_, 7);
lean_ctor_set(v___x_5350_, 1, v___x_5366_);
lean_ctor_set(v___x_5350_, 0, v___x_5360_);
v___x_5368_ = v___x_5350_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v___x_5360_);
lean_ctor_set(v_reuseFailAlloc_5382_, 1, v___x_5366_);
v___x_5368_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
lean_object* v___x_5369_; 
v___x_5369_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__7(v_cls_5316_, v___x_5368_, v_snd_5348_, v___y_5318_, v___y_5319_);
if (lean_obj_tag(v___x_5369_) == 0)
{
lean_object* v_a_5370_; lean_object* v_fst_5371_; lean_object* v_snd_5372_; lean_object* v___x_5373_; 
v_a_5370_ = lean_ctor_get(v___x_5369_, 0);
lean_inc(v_a_5370_);
lean_dec_ref_known(v___x_5369_, 1);
v_fst_5371_ = lean_ctor_get(v_a_5370_, 0);
lean_inc(v_fst_5371_);
v_snd_5372_ = lean_ctor_get(v_a_5370_, 1);
lean_inc(v_snd_5372_);
lean_dec(v_a_5370_);
v___x_5373_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_5353_, v_newArgs_5354_, v_fst_5371_, v_snd_5372_, v___y_5318_, v___y_5319_);
v___y_5276_ = v___x_5373_;
goto v___jp_5275_;
}
else
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
lean_dec_ref(v_newArgs_5354_);
lean_dec_ref(v_newDecls_5353_);
v_a_5374_ = lean_ctor_get(v___x_5369_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5369_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5376_ = v___x_5369_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5369_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5374_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
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
lean_object* v_a_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5392_; 
v_a_5385_ = lean_ctor_get(v___x_5346_, 0);
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5346_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5387_ = v___x_5346_;
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_a_5385_);
lean_dec(v___x_5346_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
lean_object* v___x_5390_; 
if (v_isShared_5388_ == 0)
{
v___x_5390_ = v___x_5387_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_a_5385_);
v___x_5390_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
return v___x_5390_;
}
}
}
}
else
{
lean_object* v_a_5393_; lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5400_; 
lean_dec(v_fst_5337_);
v_a_5393_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5400_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5400_ == 0)
{
v___x_5395_ = v___x_5343_;
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
else
{
lean_inc(v_a_5393_);
lean_dec(v___x_5343_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
lean_object* v___x_5398_; 
if (v_isShared_5396_ == 0)
{
v___x_5398_ = v___x_5395_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
return v___x_5398_;
}
}
}
}
else
{
lean_object* v_a_5401_; lean_object* v___x_5403_; uint8_t v_isShared_5404_; uint8_t v_isSharedCheck_5408_; 
lean_dec_ref(v_sortedDecls_5268_);
v_a_5401_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5408_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5408_ == 0)
{
v___x_5403_ = v___x_5335_;
v_isShared_5404_ = v_isSharedCheck_5408_;
goto v_resetjp_5402_;
}
else
{
lean_inc(v_a_5401_);
lean_dec(v___x_5335_);
v___x_5403_ = lean_box(0);
v_isShared_5404_ = v_isSharedCheck_5408_;
goto v_resetjp_5402_;
}
v_resetjp_5402_:
{
lean_object* v___x_5406_; 
if (v_isShared_5404_ == 0)
{
v___x_5406_ = v___x_5403_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5401_);
v___x_5406_ = v_reuseFailAlloc_5407_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
return v___x_5406_;
}
}
}
}
}
}
else
{
lean_object* v_a_5412_; lean_object* v___x_5414_; uint8_t v_isShared_5415_; uint8_t v_isSharedCheck_5419_; 
lean_dec_ref(v_toSortArgs_5271_);
lean_dec_ref(v_sortedDecls_5268_);
v_a_5412_ = lean_ctor_get(v___x_5325_, 0);
v_isSharedCheck_5419_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5419_ == 0)
{
v___x_5414_ = v___x_5325_;
v_isShared_5415_ = v_isSharedCheck_5419_;
goto v_resetjp_5413_;
}
else
{
lean_inc(v_a_5412_);
lean_dec(v___x_5325_);
v___x_5414_ = lean_box(0);
v_isShared_5415_ = v_isSharedCheck_5419_;
goto v_resetjp_5413_;
}
v_resetjp_5413_:
{
lean_object* v___x_5417_; 
if (v_isShared_5415_ == 0)
{
v___x_5417_ = v___x_5414_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v_a_5412_);
v___x_5417_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
return v___x_5417_;
}
}
}
}
}
else
{
lean_object* v___x_5432_; lean_object* v___x_5433_; 
lean_dec_ref(v_toSortArgs_5271_);
v___x_5432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5432_, 0, v_sortedDecls_5268_);
lean_ctor_set(v___x_5432_, 1, v_sortedArgs_5269_);
v___x_5433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5433_, 0, v___x_5432_);
return v___x_5433_;
}
}
}
v___jp_5275_:
{
if (lean_obj_tag(v___y_5276_) == 0)
{
lean_object* v_a_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5285_; 
v_a_5277_ = lean_ctor_get(v___y_5276_, 0);
v_isSharedCheck_5285_ = !lean_is_exclusive(v___y_5276_);
if (v_isSharedCheck_5285_ == 0)
{
v___x_5279_ = v___y_5276_;
v_isShared_5280_ = v_isSharedCheck_5285_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_a_5277_);
lean_dec(v___y_5276_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5285_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v_fst_5281_; lean_object* v___x_5283_; 
v_fst_5281_ = lean_ctor_get(v_a_5277_, 0);
lean_inc(v_fst_5281_);
lean_dec(v_a_5277_);
if (v_isShared_5280_ == 0)
{
lean_ctor_set(v___x_5279_, 0, v_fst_5281_);
v___x_5283_ = v___x_5279_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v_fst_5281_);
v___x_5283_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
return v___x_5283_;
}
}
}
else
{
lean_object* v_a_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5293_; 
v_a_5286_ = lean_ctor_get(v___y_5276_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___y_5276_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5288_ = v___y_5276_;
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_a_5286_);
lean_dec(v___y_5276_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v___x_5291_; 
if (v_isShared_5289_ == 0)
{
v___x_5291_ = v___x_5288_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
}
v___jp_5294_:
{
lean_object* v___x_5300_; 
lean_inc(v___y_5295_);
lean_inc_ref(v___y_5298_);
v___x_5300_ = lean_apply_5(v___y_5297_, v___y_5296_, v_snd_5299_, v___y_5298_, v___y_5295_, lean_box(0));
v___y_5276_ = v___x_5300_;
goto v___jp_5275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object* v_sortedDecls_5434_, lean_object* v_sortedArgs_5435_, lean_object* v_toSortDecls_5436_, lean_object* v_toSortArgs_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_){
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v_sortedDecls_5434_, v_sortedArgs_5435_, v_toSortDecls_5436_, v_toSortArgs_5437_, v_a_5438_, v_a_5439_);
lean_dec(v_a_5439_);
lean_dec_ref(v_a_5438_);
lean_dec_ref(v_toSortDecls_5436_);
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object* v_as_5442_, size_t v_sz_5443_, size_t v_i_5444_, lean_object* v_b_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_){
_start:
{
lean_object* v___x_5449_; 
v___x_5449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___redArg(v_as_5442_, v_sz_5443_, v_i_5444_, v_b_5445_);
return v___x_5449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___boxed(lean_object* v_as_5450_, lean_object* v_sz_5451_, lean_object* v_i_5452_, lean_object* v_b_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_){
_start:
{
size_t v_sz_boxed_5457_; size_t v_i_boxed_5458_; lean_object* v_res_5459_; 
v_sz_boxed_5457_ = lean_unbox_usize(v_sz_5451_);
lean_dec(v_sz_5451_);
v_i_boxed_5458_ = lean_unbox_usize(v_i_5452_);
lean_dec(v_i_5452_);
v_res_5459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v_as_5450_, v_sz_boxed_5457_, v_i_boxed_5458_, v_b_5453_, v___y_5454_, v___y_5455_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
lean_dec_ref(v_as_5450_);
return v_res_5459_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object* v_msg_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_){
_start:
{
lean_object* v___f_5467_; lean_object* v___x_1327__overap_5468_; lean_object* v___x_5469_; 
v___f_5467_ = ((lean_object*)(l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0));
v___x_1327__overap_5468_ = lean_panic_fn_borrowed(v___f_5467_, v_msg_5461_);
lean_inc(v___y_5465_);
lean_inc_ref(v___y_5464_);
lean_inc(v___y_5463_);
lean_inc_ref(v___y_5462_);
v___x_5469_ = lean_apply_5(v___x_1327__overap_5468_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, lean_box(0));
return v___x_5469_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object* v_msg_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_){
_start:
{
lean_object* v_res_5476_; 
v_res_5476_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_msg_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_);
lean_dec(v___y_5474_);
lean_dec_ref(v___y_5473_);
lean_dec(v___y_5472_);
lean_dec_ref(v___y_5471_);
return v_res_5476_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0(void){
_start:
{
lean_object* v_cellCount_5477_; lean_object* v___x_5478_; 
v_cellCount_5477_ = lean_unsigned_to_nat(16u);
v___x_5478_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_5477_);
return v___x_5478_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1(void){
_start:
{
lean_object* v_cellCount_5479_; lean_object* v___x_5480_; 
v_cellCount_5479_ = lean_unsigned_to_nat(16u);
v___x_5480_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_5479_);
return v___x_5480_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__2(void){
_start:
{
lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; 
v___x_5481_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
v___x_5482_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0);
v___x_5483_ = lean_unsigned_to_nat(0u);
v___x_5484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5484_, 0, v___x_5483_);
lean_ctor_set(v___x_5484_, 1, v___x_5482_);
lean_ctor_set(v___x_5484_, 2, v___x_5481_);
return v___x_5484_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__4(void){
_start:
{
lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; 
v___x_5487_ = lean_unsigned_to_nat(1u);
v___x_5488_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__3));
v___x_5489_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__2, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__2_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__2);
v___x_5490_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_5490_, 0, v___x_5489_);
lean_ctor_set(v___x_5490_, 1, v___x_5489_);
lean_ctor_set(v___x_5490_, 2, v___x_5488_);
lean_ctor_set(v___x_5490_, 3, v___x_5487_);
lean_ctor_set(v___x_5490_, 4, v___x_5488_);
lean_ctor_set(v___x_5490_, 5, v___x_5488_);
lean_ctor_set(v___x_5490_, 6, v___x_5488_);
lean_ctor_set(v___x_5490_, 7, v___x_5488_);
lean_ctor_set(v___x_5490_, 8, v___x_5487_);
lean_ctor_set(v___x_5490_, 9, v___x_5488_);
lean_ctor_set(v___x_5490_, 10, v___x_5488_);
lean_ctor_set(v___x_5490_, 11, v___x_5488_);
return v___x_5490_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__7(void){
_start:
{
lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
v___x_5493_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__6));
v___x_5494_ = lean_unsigned_to_nat(2u);
v___x_5495_ = lean_unsigned_to_nat(417u);
v___x_5496_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5));
v___x_5497_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3));
v___x_5498_ = l_mkPanicMessageWithDecl(v___x_5497_, v___x_5496_, v___x_5495_, v___x_5494_, v___x_5493_);
return v___x_5498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* v_type_5499_, lean_object* v_value_5500_, uint8_t v_zetaDelta_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_, lean_object* v_a_5505_){
_start:
{
lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; 
v___x_5507_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__4, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__4_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__4);
v___x_5508_ = lean_st_mk_ref(v___x_5507_);
v___x_5509_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_5499_, v_value_5500_, v_zetaDelta_5501_, v___x_5508_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_);
if (lean_obj_tag(v___x_5509_) == 0)
{
lean_object* v_a_5510_; lean_object* v___x_5511_; lean_object* v_fst_5512_; lean_object* v_snd_5513_; lean_object* v_levelParams_5514_; lean_object* v_levelArgs_5515_; lean_object* v_newLocalDecls_5516_; lean_object* v_newLocalDeclsForMVars_5517_; lean_object* v_newLetDecls_5518_; lean_object* v_exprMVarArgs_5519_; lean_object* v_exprFVarArgs_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; 
v_a_5510_ = lean_ctor_get(v___x_5509_, 0);
lean_inc(v_a_5510_);
lean_dec_ref_known(v___x_5509_, 1);
v___x_5511_ = lean_st_ref_get(v___x_5508_);
lean_dec(v___x_5508_);
v_fst_5512_ = lean_ctor_get(v_a_5510_, 0);
lean_inc(v_fst_5512_);
v_snd_5513_ = lean_ctor_get(v_a_5510_, 1);
lean_inc(v_snd_5513_);
lean_dec(v_a_5510_);
v_levelParams_5514_ = lean_ctor_get(v___x_5511_, 2);
lean_inc_ref(v_levelParams_5514_);
v_levelArgs_5515_ = lean_ctor_get(v___x_5511_, 4);
lean_inc_ref(v_levelArgs_5515_);
v_newLocalDecls_5516_ = lean_ctor_get(v___x_5511_, 5);
lean_inc_ref(v_newLocalDecls_5516_);
v_newLocalDeclsForMVars_5517_ = lean_ctor_get(v___x_5511_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_5517_);
v_newLetDecls_5518_ = lean_ctor_get(v___x_5511_, 7);
lean_inc_ref(v_newLetDecls_5518_);
v_exprMVarArgs_5519_ = lean_ctor_get(v___x_5511_, 9);
lean_inc_ref(v_exprMVarArgs_5519_);
v_exprFVarArgs_5520_ = lean_ctor_get(v___x_5511_, 10);
lean_inc_ref(v_exprFVarArgs_5520_);
lean_dec(v___x_5511_);
v___x_5521_ = l_Array_reverse___redArg(v_newLocalDecls_5516_);
v___x_5522_ = l_Array_reverse___redArg(v_exprFVarArgs_5520_);
v___x_5523_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v___x_5521_, v___x_5522_, v_newLocalDeclsForMVars_5517_, v_exprMVarArgs_5519_, v_a_5504_, v_a_5505_);
lean_dec_ref(v_newLocalDeclsForMVars_5517_);
if (lean_obj_tag(v___x_5523_) == 0)
{
lean_object* v_a_5524_; lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5542_; 
v_a_5524_ = lean_ctor_get(v___x_5523_, 0);
v_isSharedCheck_5542_ = !lean_is_exclusive(v___x_5523_);
if (v_isSharedCheck_5542_ == 0)
{
v___x_5526_ = v___x_5523_;
v_isShared_5527_ = v_isSharedCheck_5542_;
goto v_resetjp_5525_;
}
else
{
lean_inc(v_a_5524_);
lean_dec(v___x_5523_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5542_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v_fst_5528_; lean_object* v_snd_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; uint8_t v___x_5535_; 
v_fst_5528_ = lean_ctor_get(v_a_5524_, 0);
lean_inc_n(v_fst_5528_, 2);
v_snd_5529_ = lean_ctor_get(v_a_5524_, 1);
lean_inc(v_snd_5529_);
lean_dec(v_a_5524_);
v___x_5530_ = l_Array_reverse___redArg(v_newLetDecls_5518_);
lean_inc_ref(v___x_5530_);
v___x_5531_ = l_Lean_Meta_Closure_mkForall(v___x_5530_, v_fst_5512_);
lean_dec(v_fst_5512_);
v___x_5532_ = l_Lean_Meta_Closure_mkForall(v_fst_5528_, v___x_5531_);
lean_dec_ref(v___x_5531_);
v___x_5533_ = l_Lean_Meta_Closure_mkLambda(v___x_5530_, v_snd_5513_);
lean_dec(v_snd_5513_);
v___x_5534_ = l_Lean_Meta_Closure_mkLambda(v_fst_5528_, v___x_5533_);
lean_dec_ref(v___x_5533_);
v___x_5535_ = l_Lean_Expr_hasFVar(v___x_5534_);
if (v___x_5535_ == 0)
{
lean_object* v___x_5536_; lean_object* v___x_5538_; 
v___x_5536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5536_, 0, v_levelParams_5514_);
lean_ctor_set(v___x_5536_, 1, v___x_5532_);
lean_ctor_set(v___x_5536_, 2, v___x_5534_);
lean_ctor_set(v___x_5536_, 3, v_levelArgs_5515_);
lean_ctor_set(v___x_5536_, 4, v_snd_5529_);
if (v_isShared_5527_ == 0)
{
lean_ctor_set(v___x_5526_, 0, v___x_5536_);
v___x_5538_ = v___x_5526_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v___x_5536_);
v___x_5538_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
return v___x_5538_;
}
}
else
{
lean_object* v___x_5540_; lean_object* v___x_5541_; 
lean_dec_ref(v___x_5534_);
lean_dec_ref(v___x_5532_);
lean_dec(v_snd_5529_);
lean_del_object(v___x_5526_);
lean_dec_ref(v_levelArgs_5515_);
lean_dec_ref(v_levelParams_5514_);
v___x_5540_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__7, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__7_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__7);
v___x_5541_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v___x_5540_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_);
return v___x_5541_;
}
}
}
else
{
lean_object* v_a_5543_; lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5550_; 
lean_dec_ref(v_newLetDecls_5518_);
lean_dec_ref(v_levelArgs_5515_);
lean_dec_ref(v_levelParams_5514_);
lean_dec(v_snd_5513_);
lean_dec(v_fst_5512_);
v_a_5543_ = lean_ctor_get(v___x_5523_, 0);
v_isSharedCheck_5550_ = !lean_is_exclusive(v___x_5523_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5545_ = v___x_5523_;
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
else
{
lean_inc(v_a_5543_);
lean_dec(v___x_5523_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
lean_object* v___x_5548_; 
if (v_isShared_5546_ == 0)
{
v___x_5548_ = v___x_5545_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_a_5543_);
v___x_5548_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
return v___x_5548_;
}
}
}
}
else
{
lean_object* v_a_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5558_; 
lean_dec(v___x_5508_);
v_a_5551_ = lean_ctor_get(v___x_5509_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5509_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5553_ = v___x_5509_;
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_a_5551_);
lean_dec(v___x_5509_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5556_; 
if (v_isShared_5554_ == 0)
{
v___x_5556_ = v___x_5553_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_a_5551_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* v_type_5559_, lean_object* v_value_5560_, lean_object* v_zetaDelta_5561_, lean_object* v_a_5562_, lean_object* v_a_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_){
_start:
{
uint8_t v_zetaDelta_boxed_5567_; lean_object* v_res_5568_; 
v_zetaDelta_boxed_5567_ = lean_unbox(v_zetaDelta_5561_);
v_res_5568_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_5559_, v_value_5560_, v_zetaDelta_boxed_5567_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
return v_res_5568_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* v_name_5569_, lean_object* v_levelParams_5570_, lean_object* v_type_5571_, lean_object* v_value_5572_, lean_object* v_hints_5573_, lean_object* v___y_5574_){
_start:
{
lean_object* v___x_5576_; uint8_t v___y_5578_; uint8_t v___y_5585_; lean_object* v_env_5588_; uint8_t v___x_5589_; 
v___x_5576_ = lean_st_ref_get(v___y_5574_);
v_env_5588_ = lean_ctor_get(v___x_5576_, 0);
lean_inc_ref_n(v_env_5588_, 2);
lean_dec(v___x_5576_);
v___x_5589_ = l_Lean_Environment_hasUnsafe(v_env_5588_, v_type_5571_);
if (v___x_5589_ == 0)
{
uint8_t v___x_5590_; 
v___x_5590_ = l_Lean_Environment_hasUnsafe(v_env_5588_, v_value_5572_);
v___y_5585_ = v___x_5590_;
goto v___jp_5584_;
}
else
{
lean_dec_ref(v_env_5588_);
v___y_5585_ = v___x_5589_;
goto v___jp_5584_;
}
v___jp_5577_:
{
lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; 
lean_inc(v_name_5569_);
v___x_5579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5579_, 0, v_name_5569_);
lean_ctor_set(v___x_5579_, 1, v_levelParams_5570_);
lean_ctor_set(v___x_5579_, 2, v_type_5571_);
v___x_5580_ = lean_box(0);
v___x_5581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5581_, 0, v_name_5569_);
lean_ctor_set(v___x_5581_, 1, v___x_5580_);
v___x_5582_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_5582_, 0, v___x_5579_);
lean_ctor_set(v___x_5582_, 1, v_value_5572_);
lean_ctor_set(v___x_5582_, 2, v_hints_5573_);
lean_ctor_set(v___x_5582_, 3, v___x_5581_);
lean_ctor_set_uint8(v___x_5582_, sizeof(void*)*4, v___y_5578_);
v___x_5583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5583_, 0, v___x_5582_);
return v___x_5583_;
}
v___jp_5584_:
{
if (v___y_5585_ == 0)
{
uint8_t v___x_5586_; 
v___x_5586_ = 1;
v___y_5578_ = v___x_5586_;
goto v___jp_5577_;
}
else
{
uint8_t v___x_5587_; 
v___x_5587_ = 0;
v___y_5578_ = v___x_5587_;
goto v___jp_5577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* v_name_5591_, lean_object* v_levelParams_5592_, lean_object* v_type_5593_, lean_object* v_value_5594_, lean_object* v_hints_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_){
_start:
{
lean_object* v_res_5598_; 
v_res_5598_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_5591_, v_levelParams_5592_, v_type_5593_, v_value_5594_, v_hints_5595_, v___y_5596_);
lean_dec(v___y_5596_);
return v_res_5598_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(lean_object* v_name_5599_, lean_object* v_levelParams_5600_, lean_object* v_type_5601_, lean_object* v_value_5602_, lean_object* v_hints_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_){
_start:
{
lean_object* v___x_5609_; 
v___x_5609_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_5599_, v_levelParams_5600_, v_type_5601_, v_value_5602_, v_hints_5603_, v___y_5607_);
return v___x_5609_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* v_name_5610_, lean_object* v_levelParams_5611_, lean_object* v_type_5612_, lean_object* v_value_5613_, lean_object* v_hints_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_){
_start:
{
lean_object* v_res_5620_; 
v_res_5620_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(v_name_5610_, v_levelParams_5611_, v_type_5612_, v_value_5613_, v_hints_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_);
lean_dec(v___y_5618_);
lean_dec_ref(v___y_5617_);
lean_dec(v___y_5616_);
lean_dec_ref(v___y_5615_);
return v_res_5620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* v_name_5621_, lean_object* v_type_5622_, lean_object* v_value_5623_, uint8_t v_zetaDelta_5624_, uint8_t v_compile_5625_, uint8_t v_logCompileErrors_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_){
_start:
{
lean_object* v___x_5632_; 
v___x_5632_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_5622_, v_value_5623_, v_zetaDelta_5624_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_);
if (lean_obj_tag(v___x_5632_) == 0)
{
lean_object* v_a_5633_; lean_object* v___x_5635_; uint8_t v_isShared_5636_; uint8_t v_isSharedCheck_5684_; 
v_a_5633_ = lean_ctor_get(v___x_5632_, 0);
v_isSharedCheck_5684_ = !lean_is_exclusive(v___x_5632_);
if (v_isSharedCheck_5684_ == 0)
{
v___x_5635_ = v___x_5632_;
v_isShared_5636_ = v_isSharedCheck_5684_;
goto v_resetjp_5634_;
}
else
{
lean_inc(v_a_5633_);
lean_dec(v___x_5632_);
v___x_5635_ = lean_box(0);
v_isShared_5636_ = v_isSharedCheck_5684_;
goto v_resetjp_5634_;
}
v_resetjp_5634_:
{
lean_object* v___x_5637_; lean_object* v_env_5638_; lean_object* v_levelParams_5639_; lean_object* v_type_5640_; lean_object* v_value_5641_; lean_object* v_levelArgs_5642_; lean_object* v_exprArgs_5643_; uint32_t v___x_5651_; uint32_t v___x_5652_; uint32_t v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v_a_5657_; lean_object* v___x_5659_; uint8_t v_isShared_5660_; uint8_t v_isSharedCheck_5683_; 
v___x_5637_ = lean_st_ref_get(v_a_5630_);
v_env_5638_ = lean_ctor_get(v___x_5637_, 0);
lean_inc_ref(v_env_5638_);
lean_dec(v___x_5637_);
v_levelParams_5639_ = lean_ctor_get(v_a_5633_, 0);
lean_inc_ref(v_levelParams_5639_);
v_type_5640_ = lean_ctor_get(v_a_5633_, 1);
lean_inc_ref(v_type_5640_);
v_value_5641_ = lean_ctor_get(v_a_5633_, 2);
lean_inc_ref_n(v_value_5641_, 2);
v_levelArgs_5642_ = lean_ctor_get(v_a_5633_, 3);
lean_inc_ref(v_levelArgs_5642_);
v_exprArgs_5643_ = lean_ctor_get(v_a_5633_, 4);
lean_inc_ref(v_exprArgs_5643_);
lean_dec(v_a_5633_);
v___x_5651_ = l_Lean_getMaxHeight(v_env_5638_, v_value_5641_);
v___x_5652_ = 1;
v___x_5653_ = lean_uint32_add(v___x_5651_, v___x_5652_);
v___x_5654_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_5654_, 0, v___x_5653_);
v___x_5655_ = lean_array_to_list(v_levelParams_5639_);
lean_inc(v_name_5621_);
v___x_5656_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_5621_, v___x_5655_, v_type_5640_, v_value_5641_, v___x_5654_, v_a_5630_);
v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
v_isSharedCheck_5683_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5683_ == 0)
{
v___x_5659_ = v___x_5656_;
v_isShared_5660_ = v_isSharedCheck_5683_;
goto v_resetjp_5658_;
}
else
{
lean_inc(v_a_5657_);
lean_dec(v___x_5656_);
v___x_5659_ = lean_box(0);
v_isShared_5660_ = v_isSharedCheck_5683_;
goto v_resetjp_5658_;
}
v___jp_5644_:
{
lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5649_; 
v___x_5645_ = lean_array_to_list(v_levelArgs_5642_);
v___x_5646_ = l_Lean_mkConst(v_name_5621_, v___x_5645_);
v___x_5647_ = l_Lean_mkAppN(v___x_5646_, v_exprArgs_5643_);
lean_dec_ref(v_exprArgs_5643_);
if (v_isShared_5636_ == 0)
{
lean_ctor_set(v___x_5635_, 0, v___x_5647_);
v___x_5649_ = v___x_5635_;
goto v_reusejp_5648_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v___x_5647_);
v___x_5649_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5648_;
}
v_reusejp_5648_:
{
return v___x_5649_;
}
}
v_resetjp_5658_:
{
lean_object* v___x_5662_; 
if (v_isShared_5660_ == 0)
{
lean_ctor_set_tag(v___x_5659_, 1);
v___x_5662_ = v___x_5659_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5682_; 
v_reuseFailAlloc_5682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_a_5657_);
v___x_5662_ = v_reuseFailAlloc_5682_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
uint8_t v___x_5663_; lean_object* v___x_5664_; 
v___x_5663_ = 0;
lean_inc_ref(v___x_5662_);
v___x_5664_ = l_Lean_addDecl(v___x_5662_, v___x_5663_, v_a_5629_, v_a_5630_);
if (lean_obj_tag(v___x_5664_) == 0)
{
lean_dec_ref_known(v___x_5664_, 1);
if (v_compile_5625_ == 0)
{
lean_dec_ref(v___x_5662_);
goto v___jp_5644_;
}
else
{
lean_object* v___x_5665_; 
v___x_5665_ = l_Lean_compileDecl(v___x_5662_, v_logCompileErrors_5626_, v_a_5629_, v_a_5630_);
if (lean_obj_tag(v___x_5665_) == 0)
{
lean_dec_ref_known(v___x_5665_, 1);
goto v___jp_5644_;
}
else
{
lean_object* v_a_5666_; lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5673_; 
lean_dec_ref(v_exprArgs_5643_);
lean_dec_ref(v_levelArgs_5642_);
lean_del_object(v___x_5635_);
lean_dec(v_name_5621_);
v_a_5666_ = lean_ctor_get(v___x_5665_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5665_);
if (v_isSharedCheck_5673_ == 0)
{
v___x_5668_ = v___x_5665_;
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
else
{
lean_inc(v_a_5666_);
lean_dec(v___x_5665_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5671_; 
if (v_isShared_5669_ == 0)
{
v___x_5671_ = v___x_5668_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_a_5666_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
return v___x_5671_;
}
}
}
}
}
else
{
lean_object* v_a_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5681_; 
lean_dec_ref(v___x_5662_);
lean_dec_ref(v_exprArgs_5643_);
lean_dec_ref(v_levelArgs_5642_);
lean_del_object(v___x_5635_);
lean_dec(v_name_5621_);
v_a_5674_ = lean_ctor_get(v___x_5664_, 0);
v_isSharedCheck_5681_ = !lean_is_exclusive(v___x_5664_);
if (v_isSharedCheck_5681_ == 0)
{
v___x_5676_ = v___x_5664_;
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_a_5674_);
lean_dec(v___x_5664_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5679_; 
if (v_isShared_5677_ == 0)
{
v___x_5679_ = v___x_5676_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_a_5674_);
v___x_5679_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
return v___x_5679_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5685_; lean_object* v___x_5687_; uint8_t v_isShared_5688_; uint8_t v_isSharedCheck_5692_; 
lean_dec(v_name_5621_);
v_a_5685_ = lean_ctor_get(v___x_5632_, 0);
v_isSharedCheck_5692_ = !lean_is_exclusive(v___x_5632_);
if (v_isSharedCheck_5692_ == 0)
{
v___x_5687_ = v___x_5632_;
v_isShared_5688_ = v_isSharedCheck_5692_;
goto v_resetjp_5686_;
}
else
{
lean_inc(v_a_5685_);
lean_dec(v___x_5632_);
v___x_5687_ = lean_box(0);
v_isShared_5688_ = v_isSharedCheck_5692_;
goto v_resetjp_5686_;
}
v_resetjp_5686_:
{
lean_object* v___x_5690_; 
if (v_isShared_5688_ == 0)
{
v___x_5690_ = v___x_5687_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5691_; 
v_reuseFailAlloc_5691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5691_, 0, v_a_5685_);
v___x_5690_ = v_reuseFailAlloc_5691_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
return v___x_5690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* v_name_5693_, lean_object* v_type_5694_, lean_object* v_value_5695_, lean_object* v_zetaDelta_5696_, lean_object* v_compile_5697_, lean_object* v_logCompileErrors_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_){
_start:
{
uint8_t v_zetaDelta_boxed_5704_; uint8_t v_compile_boxed_5705_; uint8_t v_logCompileErrors_boxed_5706_; lean_object* v_res_5707_; 
v_zetaDelta_boxed_5704_ = lean_unbox(v_zetaDelta_5696_);
v_compile_boxed_5705_ = lean_unbox(v_compile_5697_);
v_logCompileErrors_boxed_5706_ = lean_unbox(v_logCompileErrors_5698_);
v_res_5707_ = l_Lean_Meta_mkAuxDefinition(v_name_5693_, v_type_5694_, v_value_5695_, v_zetaDelta_boxed_5704_, v_compile_boxed_5705_, v_logCompileErrors_boxed_5706_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
lean_dec(v_a_5702_);
lean_dec_ref(v_a_5701_);
lean_dec(v_a_5700_);
lean_dec_ref(v_a_5699_);
return v_res_5707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* v_name_5708_, lean_object* v_value_5709_, uint8_t v_zetaDelta_5710_, uint8_t v_compile_5711_, uint8_t v_logCompileErrors_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_){
_start:
{
lean_object* v___x_5718_; 
lean_inc(v_a_5716_);
lean_inc_ref(v_a_5715_);
lean_inc(v_a_5714_);
lean_inc_ref(v_a_5713_);
lean_inc_ref(v_value_5709_);
v___x_5718_ = lean_infer_type(v_value_5709_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_);
if (lean_obj_tag(v___x_5718_) == 0)
{
lean_object* v_a_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; 
v_a_5719_ = lean_ctor_get(v___x_5718_, 0);
lean_inc(v_a_5719_);
lean_dec_ref_known(v___x_5718_, 1);
v___x_5720_ = l_Lean_Expr_headBeta(v_a_5719_);
v___x_5721_ = l_Lean_Meta_mkAuxDefinition(v_name_5708_, v___x_5720_, v_value_5709_, v_zetaDelta_5710_, v_compile_5711_, v_logCompileErrors_5712_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_);
return v___x_5721_;
}
else
{
lean_dec_ref(v_value_5709_);
lean_dec(v_name_5708_);
return v___x_5718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* v_name_5722_, lean_object* v_value_5723_, lean_object* v_zetaDelta_5724_, lean_object* v_compile_5725_, lean_object* v_logCompileErrors_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_){
_start:
{
uint8_t v_zetaDelta_boxed_5732_; uint8_t v_compile_boxed_5733_; uint8_t v_logCompileErrors_boxed_5734_; lean_object* v_res_5735_; 
v_zetaDelta_boxed_5732_ = lean_unbox(v_zetaDelta_5724_);
v_compile_boxed_5733_ = lean_unbox(v_compile_5725_);
v_logCompileErrors_boxed_5734_ = lean_unbox(v_logCompileErrors_5726_);
v_res_5735_ = l_Lean_Meta_mkAuxDefinitionFor(v_name_5722_, v_value_5723_, v_zetaDelta_boxed_5732_, v_compile_boxed_5733_, v_logCompileErrors_boxed_5734_, v_a_5727_, v_a_5728_, v_a_5729_, v_a_5730_);
lean_dec(v_a_5730_);
lean_dec_ref(v_a_5729_);
lean_dec(v_a_5728_);
lean_dec_ref(v_a_5727_);
return v_res_5735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* v_type_5736_, lean_object* v_value_5737_, uint8_t v_zetaDelta_5738_, lean_object* v_kind_x3f_5739_, uint8_t v_cache_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_){
_start:
{
lean_object* v___x_5746_; 
v___x_5746_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_5736_, v_value_5737_, v_zetaDelta_5738_, v_a_5741_, v_a_5742_, v_a_5743_, v_a_5744_);
if (lean_obj_tag(v___x_5746_) == 0)
{
lean_object* v_a_5747_; lean_object* v_levelParams_5748_; lean_object* v_type_5749_; lean_object* v_value_5750_; lean_object* v_levelArgs_5751_; lean_object* v_exprArgs_5752_; lean_object* v___x_5753_; uint8_t v___x_5754_; lean_object* v___x_5755_; 
v_a_5747_ = lean_ctor_get(v___x_5746_, 0);
lean_inc(v_a_5747_);
lean_dec_ref_known(v___x_5746_, 1);
v_levelParams_5748_ = lean_ctor_get(v_a_5747_, 0);
lean_inc_ref(v_levelParams_5748_);
v_type_5749_ = lean_ctor_get(v_a_5747_, 1);
lean_inc_ref(v_type_5749_);
v_value_5750_ = lean_ctor_get(v_a_5747_, 2);
lean_inc_ref(v_value_5750_);
v_levelArgs_5751_ = lean_ctor_get(v_a_5747_, 3);
lean_inc_ref(v_levelArgs_5751_);
v_exprArgs_5752_ = lean_ctor_get(v_a_5747_, 4);
lean_inc_ref(v_exprArgs_5752_);
lean_dec(v_a_5747_);
v___x_5753_ = lean_array_to_list(v_levelParams_5748_);
v___x_5754_ = 0;
v___x_5755_ = l_Lean_Meta_mkAuxLemma(v___x_5753_, v_type_5749_, v_value_5750_, v_kind_x3f_5739_, v_cache_5740_, v___x_5754_, v___x_5754_, v___x_5754_, v_a_5741_, v_a_5742_, v_a_5743_, v_a_5744_);
if (lean_obj_tag(v___x_5755_) == 0)
{
lean_object* v_a_5756_; lean_object* v___x_5758_; uint8_t v_isShared_5759_; uint8_t v_isSharedCheck_5766_; 
v_a_5756_ = lean_ctor_get(v___x_5755_, 0);
v_isSharedCheck_5766_ = !lean_is_exclusive(v___x_5755_);
if (v_isSharedCheck_5766_ == 0)
{
v___x_5758_ = v___x_5755_;
v_isShared_5759_ = v_isSharedCheck_5766_;
goto v_resetjp_5757_;
}
else
{
lean_inc(v_a_5756_);
lean_dec(v___x_5755_);
v___x_5758_ = lean_box(0);
v_isShared_5759_ = v_isSharedCheck_5766_;
goto v_resetjp_5757_;
}
v_resetjp_5757_:
{
lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5764_; 
v___x_5760_ = lean_array_to_list(v_levelArgs_5751_);
v___x_5761_ = l_Lean_mkConst(v_a_5756_, v___x_5760_);
v___x_5762_ = l_Lean_mkAppN(v___x_5761_, v_exprArgs_5752_);
lean_dec_ref(v_exprArgs_5752_);
if (v_isShared_5759_ == 0)
{
lean_ctor_set(v___x_5758_, 0, v___x_5762_);
v___x_5764_ = v___x_5758_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v___x_5762_);
v___x_5764_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
return v___x_5764_;
}
}
}
else
{
lean_object* v_a_5767_; lean_object* v___x_5769_; uint8_t v_isShared_5770_; uint8_t v_isSharedCheck_5774_; 
lean_dec_ref(v_exprArgs_5752_);
lean_dec_ref(v_levelArgs_5751_);
v_a_5767_ = lean_ctor_get(v___x_5755_, 0);
v_isSharedCheck_5774_ = !lean_is_exclusive(v___x_5755_);
if (v_isSharedCheck_5774_ == 0)
{
v___x_5769_ = v___x_5755_;
v_isShared_5770_ = v_isSharedCheck_5774_;
goto v_resetjp_5768_;
}
else
{
lean_inc(v_a_5767_);
lean_dec(v___x_5755_);
v___x_5769_ = lean_box(0);
v_isShared_5770_ = v_isSharedCheck_5774_;
goto v_resetjp_5768_;
}
v_resetjp_5768_:
{
lean_object* v___x_5772_; 
if (v_isShared_5770_ == 0)
{
v___x_5772_ = v___x_5769_;
goto v_reusejp_5771_;
}
else
{
lean_object* v_reuseFailAlloc_5773_; 
v_reuseFailAlloc_5773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5773_, 0, v_a_5767_);
v___x_5772_ = v_reuseFailAlloc_5773_;
goto v_reusejp_5771_;
}
v_reusejp_5771_:
{
return v___x_5772_;
}
}
}
}
else
{
lean_object* v_a_5775_; lean_object* v___x_5777_; uint8_t v_isShared_5778_; uint8_t v_isSharedCheck_5782_; 
lean_dec(v_kind_x3f_5739_);
v_a_5775_ = lean_ctor_get(v___x_5746_, 0);
v_isSharedCheck_5782_ = !lean_is_exclusive(v___x_5746_);
if (v_isSharedCheck_5782_ == 0)
{
v___x_5777_ = v___x_5746_;
v_isShared_5778_ = v_isSharedCheck_5782_;
goto v_resetjp_5776_;
}
else
{
lean_inc(v_a_5775_);
lean_dec(v___x_5746_);
v___x_5777_ = lean_box(0);
v_isShared_5778_ = v_isSharedCheck_5782_;
goto v_resetjp_5776_;
}
v_resetjp_5776_:
{
lean_object* v___x_5780_; 
if (v_isShared_5778_ == 0)
{
v___x_5780_ = v___x_5777_;
goto v_reusejp_5779_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v_a_5775_);
v___x_5780_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5779_;
}
v_reusejp_5779_:
{
return v___x_5780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* v_type_5783_, lean_object* v_value_5784_, lean_object* v_zetaDelta_5785_, lean_object* v_kind_x3f_5786_, lean_object* v_cache_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_){
_start:
{
uint8_t v_zetaDelta_boxed_5793_; uint8_t v_cache_boxed_5794_; lean_object* v_res_5795_; 
v_zetaDelta_boxed_5793_ = lean_unbox(v_zetaDelta_5785_);
v_cache_boxed_5794_ = lean_unbox(v_cache_5787_);
v_res_5795_ = l_Lean_Meta_mkAuxTheorem(v_type_5783_, v_value_5784_, v_zetaDelta_boxed_5793_, v_kind_x3f_5786_, v_cache_boxed_5794_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_);
lean_dec(v_a_5791_);
lean_dec_ref(v_a_5790_);
lean_dec(v_a_5789_);
lean_dec_ref(v_a_5788_);
return v_res_5795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5851_; uint8_t v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5851_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__11));
v___x_5852_ = 0;
v___x_5853_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_));
v___x_5854_ = l_Lean_registerTraceClass(v___x_5851_, v___x_5852_, v___x_5853_);
return v___x_5854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(lean_object* v_a_5855_){
_start:
{
lean_object* v_res_5856_; 
v_res_5856_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
return v_res_5856_;
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
