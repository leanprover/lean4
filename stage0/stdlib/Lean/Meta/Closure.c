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
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__3;
static lean_once_cell_t l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0(lean_object*);
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
lean_object* v_a_369_; lean_object* v_a_371_; uint8_t v___x_407_; 
v_a_369_ = lean_ctor_get(v_x_365_, 0);
v___x_407_ = l_Lean_Level_hasMVar(v_a_369_);
if (v___x_407_ == 0)
{
uint8_t v___x_408_; 
v___x_408_ = l_Lean_Level_hasParam(v_a_369_);
if (v___x_408_ == 0)
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
lean_dec_ref_known(v_x_365_, 1);
return v___x_382_;
}
}
else
{
lean_object* v_val_406_; 
v_val_406_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v___x_381_, 1);
v_a_371_ = v_val_406_;
goto v___jp_370_;
}
}
}
case 2:
{
lean_object* v_a_409_; lean_object* v_a_410_; lean_object* v___y_412_; lean_object* v_a_413_; lean_object* v___y_427_; lean_object* v_a_457_; uint8_t v___x_489_; 
v_a_409_ = lean_ctor_get(v_x_365_, 0);
v_a_410_ = lean_ctor_get(v_x_365_, 1);
v___x_489_ = l_Lean_Level_hasMVar(v_a_409_);
if (v___x_489_ == 0)
{
uint8_t v___x_490_; 
v___x_490_ = l_Lean_Level_hasParam(v_a_409_);
if (v___x_490_ == 0)
{
lean_inc(v_a_409_);
v_a_457_ = v_a_409_;
goto v___jp_456_;
}
else
{
goto v___jp_460_;
}
}
else
{
goto v___jp_460_;
}
v___jp_411_:
{
size_t v___x_414_; size_t v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_ptr_addr(v_a_409_);
v___x_415_ = lean_ptr_addr(v___y_412_);
v___x_416_ = lean_usize_dec_eq(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref_known(v_x_365_, 2);
v___x_417_ = l_Lean_mkLevelMax_x27(v___y_412_, v_a_413_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
else
{
size_t v___x_419_; size_t v___x_420_; uint8_t v___x_421_; 
v___x_419_ = lean_ptr_addr(v_a_410_);
v___x_420_ = lean_ptr_addr(v_a_413_);
v___x_421_ = lean_usize_dec_eq(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref_known(v_x_365_, 2);
v___x_422_ = l_Lean_mkLevelMax_x27(v___y_412_, v_a_413_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = l_Lean_simpLevelMax_x27(v___y_412_, v_a_413_, v_x_365_);
lean_dec_ref_known(v_x_365_, 2);
lean_dec(v_a_413_);
lean_dec(v___y_412_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
}
v___jp_426_:
{
lean_object* v___x_428_; lean_object* v_visitedLevel_429_; lean_object* v___x_430_; 
v___x_428_ = lean_st_ref_get(v_a_366_);
v_visitedLevel_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc_ref(v_visitedLevel_429_);
lean_dec(v___x_428_);
v___x_430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_429_, v_a_410_);
lean_dec_ref(v_visitedLevel_429_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v___x_431_; 
lean_inc(v_a_410_);
v___x_431_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_410_, v_a_366_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_433_; lean_object* v_visitedLevel_434_; lean_object* v_visitedExpr_435_; lean_object* v_levelParams_436_; lean_object* v_nextLevelIdx_437_; lean_object* v_levelArgs_438_; lean_object* v_newLocalDecls_439_; lean_object* v_newLocalDeclsForMVars_440_; lean_object* v_newLetDecls_441_; lean_object* v_nextExprIdx_442_; lean_object* v_exprMVarArgs_443_; lean_object* v_exprFVarArgs_444_; lean_object* v_toProcess_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_454_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_431_, 1);
v___x_433_ = lean_st_ref_take(v_a_366_);
v_visitedLevel_434_ = lean_ctor_get(v___x_433_, 0);
v_visitedExpr_435_ = lean_ctor_get(v___x_433_, 1);
v_levelParams_436_ = lean_ctor_get(v___x_433_, 2);
v_nextLevelIdx_437_ = lean_ctor_get(v___x_433_, 3);
v_levelArgs_438_ = lean_ctor_get(v___x_433_, 4);
v_newLocalDecls_439_ = lean_ctor_get(v___x_433_, 5);
v_newLocalDeclsForMVars_440_ = lean_ctor_get(v___x_433_, 6);
v_newLetDecls_441_ = lean_ctor_get(v___x_433_, 7);
v_nextExprIdx_442_ = lean_ctor_get(v___x_433_, 8);
v_exprMVarArgs_443_ = lean_ctor_get(v___x_433_, 9);
v_exprFVarArgs_444_ = lean_ctor_get(v___x_433_, 10);
v_toProcess_445_ = lean_ctor_get(v___x_433_, 11);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_454_ == 0)
{
v___x_447_ = v___x_433_;
v_isShared_448_ = v_isSharedCheck_454_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_toProcess_445_);
lean_inc(v_exprFVarArgs_444_);
lean_inc(v_exprMVarArgs_443_);
lean_inc(v_nextExprIdx_442_);
lean_inc(v_newLetDecls_441_);
lean_inc(v_newLocalDeclsForMVars_440_);
lean_inc(v_newLocalDecls_439_);
lean_inc(v_levelArgs_438_);
lean_inc(v_nextLevelIdx_437_);
lean_inc(v_levelParams_436_);
lean_inc(v_visitedExpr_435_);
lean_inc(v_visitedLevel_434_);
lean_dec(v___x_433_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_454_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
lean_inc(v_a_432_);
lean_inc(v_a_410_);
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_434_, v_a_410_, v_a_432_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_visitedExpr_435_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_levelParams_436_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_nextLevelIdx_437_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_levelArgs_438_);
lean_ctor_set(v_reuseFailAlloc_453_, 5, v_newLocalDecls_439_);
lean_ctor_set(v_reuseFailAlloc_453_, 6, v_newLocalDeclsForMVars_440_);
lean_ctor_set(v_reuseFailAlloc_453_, 7, v_newLetDecls_441_);
lean_ctor_set(v_reuseFailAlloc_453_, 8, v_nextExprIdx_442_);
lean_ctor_set(v_reuseFailAlloc_453_, 9, v_exprMVarArgs_443_);
lean_ctor_set(v_reuseFailAlloc_453_, 10, v_exprFVarArgs_444_);
lean_ctor_set(v_reuseFailAlloc_453_, 11, v_toProcess_445_);
v___x_451_ = v_reuseFailAlloc_453_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; 
v___x_452_ = lean_st_ref_put(v_a_366_, v___x_451_);
v___y_412_ = v___y_427_;
v_a_413_ = v_a_432_;
goto v___jp_411_;
}
}
}
else
{
lean_dec(v___y_427_);
lean_dec_ref_known(v_x_365_, 2);
return v___x_431_;
}
}
else
{
lean_object* v_val_455_; 
v_val_455_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_val_455_);
lean_dec_ref_known(v___x_430_, 1);
v___y_412_ = v___y_427_;
v_a_413_ = v_val_455_;
goto v___jp_411_;
}
}
v___jp_456_:
{
uint8_t v___x_458_; 
v___x_458_ = l_Lean_Level_hasMVar(v_a_410_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; 
v___x_459_ = l_Lean_Level_hasParam(v_a_410_);
if (v___x_459_ == 0)
{
lean_inc(v_a_410_);
v___y_412_ = v_a_457_;
v_a_413_ = v_a_410_;
goto v___jp_411_;
}
else
{
v___y_427_ = v_a_457_;
goto v___jp_426_;
}
}
else
{
v___y_427_ = v_a_457_;
goto v___jp_426_;
}
}
v___jp_460_:
{
lean_object* v___x_461_; lean_object* v_visitedLevel_462_; lean_object* v___x_463_; 
v___x_461_ = lean_st_ref_get(v_a_366_);
v_visitedLevel_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc_ref(v_visitedLevel_462_);
lean_dec(v___x_461_);
v___x_463_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_462_, v_a_409_);
lean_dec_ref(v_visitedLevel_462_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_464_; 
lean_inc(v_a_409_);
v___x_464_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_409_, v_a_366_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; lean_object* v_visitedLevel_467_; lean_object* v_visitedExpr_468_; lean_object* v_levelParams_469_; lean_object* v_nextLevelIdx_470_; lean_object* v_levelArgs_471_; lean_object* v_newLocalDecls_472_; lean_object* v_newLocalDeclsForMVars_473_; lean_object* v_newLetDecls_474_; lean_object* v_nextExprIdx_475_; lean_object* v_exprMVarArgs_476_; lean_object* v_exprFVarArgs_477_; lean_object* v_toProcess_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_487_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = lean_st_ref_take(v_a_366_);
v_visitedLevel_467_ = lean_ctor_get(v___x_466_, 0);
v_visitedExpr_468_ = lean_ctor_get(v___x_466_, 1);
v_levelParams_469_ = lean_ctor_get(v___x_466_, 2);
v_nextLevelIdx_470_ = lean_ctor_get(v___x_466_, 3);
v_levelArgs_471_ = lean_ctor_get(v___x_466_, 4);
v_newLocalDecls_472_ = lean_ctor_get(v___x_466_, 5);
v_newLocalDeclsForMVars_473_ = lean_ctor_get(v___x_466_, 6);
v_newLetDecls_474_ = lean_ctor_get(v___x_466_, 7);
v_nextExprIdx_475_ = lean_ctor_get(v___x_466_, 8);
v_exprMVarArgs_476_ = lean_ctor_get(v___x_466_, 9);
v_exprFVarArgs_477_ = lean_ctor_get(v___x_466_, 10);
v_toProcess_478_ = lean_ctor_get(v___x_466_, 11);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_487_ == 0)
{
v___x_480_ = v___x_466_;
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_toProcess_478_);
lean_inc(v_exprFVarArgs_477_);
lean_inc(v_exprMVarArgs_476_);
lean_inc(v_nextExprIdx_475_);
lean_inc(v_newLetDecls_474_);
lean_inc(v_newLocalDeclsForMVars_473_);
lean_inc(v_newLocalDecls_472_);
lean_inc(v_levelArgs_471_);
lean_inc(v_nextLevelIdx_470_);
lean_inc(v_levelParams_469_);
lean_inc(v_visitedExpr_468_);
lean_inc(v_visitedLevel_467_);
lean_dec(v___x_466_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
lean_inc(v_a_465_);
lean_inc(v_a_409_);
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_467_, v_a_409_, v_a_465_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_visitedExpr_468_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_levelParams_469_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v_nextLevelIdx_470_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v_levelArgs_471_);
lean_ctor_set(v_reuseFailAlloc_486_, 5, v_newLocalDecls_472_);
lean_ctor_set(v_reuseFailAlloc_486_, 6, v_newLocalDeclsForMVars_473_);
lean_ctor_set(v_reuseFailAlloc_486_, 7, v_newLetDecls_474_);
lean_ctor_set(v_reuseFailAlloc_486_, 8, v_nextExprIdx_475_);
lean_ctor_set(v_reuseFailAlloc_486_, 9, v_exprMVarArgs_476_);
lean_ctor_set(v_reuseFailAlloc_486_, 10, v_exprFVarArgs_477_);
lean_ctor_set(v_reuseFailAlloc_486_, 11, v_toProcess_478_);
v___x_484_ = v_reuseFailAlloc_486_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_485_; 
v___x_485_ = lean_st_ref_put(v_a_366_, v___x_484_);
v_a_457_ = v_a_465_;
goto v___jp_456_;
}
}
}
else
{
lean_dec_ref_known(v_x_365_, 2);
return v___x_464_;
}
}
else
{
lean_object* v_val_488_; 
v_val_488_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v___x_463_, 1);
v_a_457_ = v_val_488_;
goto v___jp_456_;
}
}
}
case 3:
{
lean_object* v_a_491_; lean_object* v_a_492_; lean_object* v___y_494_; lean_object* v_a_495_; lean_object* v___y_509_; lean_object* v_a_539_; uint8_t v___x_571_; 
v_a_491_ = lean_ctor_get(v_x_365_, 0);
v_a_492_ = lean_ctor_get(v_x_365_, 1);
v___x_571_ = l_Lean_Level_hasMVar(v_a_491_);
if (v___x_571_ == 0)
{
uint8_t v___x_572_; 
v___x_572_ = l_Lean_Level_hasParam(v_a_491_);
if (v___x_572_ == 0)
{
lean_inc(v_a_491_);
v_a_539_ = v_a_491_;
goto v___jp_538_;
}
else
{
goto v___jp_542_;
}
}
else
{
goto v___jp_542_;
}
v___jp_493_:
{
size_t v___x_496_; size_t v___x_497_; uint8_t v___x_498_; 
v___x_496_ = lean_ptr_addr(v_a_491_);
v___x_497_ = lean_ptr_addr(v___y_494_);
v___x_498_ = lean_usize_dec_eq(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec_ref_known(v_x_365_, 2);
v___x_499_ = l_Lean_mkLevelIMax_x27(v___y_494_, v_a_495_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
else
{
size_t v___x_501_; size_t v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_ptr_addr(v_a_492_);
v___x_502_ = lean_ptr_addr(v_a_495_);
v___x_503_ = lean_usize_dec_eq(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec_ref_known(v_x_365_, 2);
v___x_504_ = l_Lean_mkLevelIMax_x27(v___y_494_, v_a_495_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = l_Lean_simpLevelIMax_x27(v___y_494_, v_a_495_, v_x_365_);
lean_dec_ref_known(v_x_365_, 2);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
}
v___jp_508_:
{
lean_object* v___x_510_; lean_object* v_visitedLevel_511_; lean_object* v___x_512_; 
v___x_510_ = lean_st_ref_get(v_a_366_);
v_visitedLevel_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc_ref(v_visitedLevel_511_);
lean_dec(v___x_510_);
v___x_512_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_511_, v_a_492_);
lean_dec_ref(v_visitedLevel_511_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v___x_513_; 
lean_inc(v_a_492_);
v___x_513_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_492_, v_a_366_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; lean_object* v_visitedLevel_516_; lean_object* v_visitedExpr_517_; lean_object* v_levelParams_518_; lean_object* v_nextLevelIdx_519_; lean_object* v_levelArgs_520_; lean_object* v_newLocalDecls_521_; lean_object* v_newLocalDeclsForMVars_522_; lean_object* v_newLetDecls_523_; lean_object* v_nextExprIdx_524_; lean_object* v_exprMVarArgs_525_; lean_object* v_exprFVarArgs_526_; lean_object* v_toProcess_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_536_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = lean_st_ref_take(v_a_366_);
v_visitedLevel_516_ = lean_ctor_get(v___x_515_, 0);
v_visitedExpr_517_ = lean_ctor_get(v___x_515_, 1);
v_levelParams_518_ = lean_ctor_get(v___x_515_, 2);
v_nextLevelIdx_519_ = lean_ctor_get(v___x_515_, 3);
v_levelArgs_520_ = lean_ctor_get(v___x_515_, 4);
v_newLocalDecls_521_ = lean_ctor_get(v___x_515_, 5);
v_newLocalDeclsForMVars_522_ = lean_ctor_get(v___x_515_, 6);
v_newLetDecls_523_ = lean_ctor_get(v___x_515_, 7);
v_nextExprIdx_524_ = lean_ctor_get(v___x_515_, 8);
v_exprMVarArgs_525_ = lean_ctor_get(v___x_515_, 9);
v_exprFVarArgs_526_ = lean_ctor_get(v___x_515_, 10);
v_toProcess_527_ = lean_ctor_get(v___x_515_, 11);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_536_ == 0)
{
v___x_529_ = v___x_515_;
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_toProcess_527_);
lean_inc(v_exprFVarArgs_526_);
lean_inc(v_exprMVarArgs_525_);
lean_inc(v_nextExprIdx_524_);
lean_inc(v_newLetDecls_523_);
lean_inc(v_newLocalDeclsForMVars_522_);
lean_inc(v_newLocalDecls_521_);
lean_inc(v_levelArgs_520_);
lean_inc(v_nextLevelIdx_519_);
lean_inc(v_levelParams_518_);
lean_inc(v_visitedExpr_517_);
lean_inc(v_visitedLevel_516_);
lean_dec(v___x_515_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_533_; 
lean_inc(v_a_514_);
lean_inc(v_a_492_);
v___x_531_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_516_, v_a_492_, v_a_514_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_531_);
v___x_533_ = v___x_529_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_visitedExpr_517_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_levelParams_518_);
lean_ctor_set(v_reuseFailAlloc_535_, 3, v_nextLevelIdx_519_);
lean_ctor_set(v_reuseFailAlloc_535_, 4, v_levelArgs_520_);
lean_ctor_set(v_reuseFailAlloc_535_, 5, v_newLocalDecls_521_);
lean_ctor_set(v_reuseFailAlloc_535_, 6, v_newLocalDeclsForMVars_522_);
lean_ctor_set(v_reuseFailAlloc_535_, 7, v_newLetDecls_523_);
lean_ctor_set(v_reuseFailAlloc_535_, 8, v_nextExprIdx_524_);
lean_ctor_set(v_reuseFailAlloc_535_, 9, v_exprMVarArgs_525_);
lean_ctor_set(v_reuseFailAlloc_535_, 10, v_exprFVarArgs_526_);
lean_ctor_set(v_reuseFailAlloc_535_, 11, v_toProcess_527_);
v___x_533_ = v_reuseFailAlloc_535_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; 
v___x_534_ = lean_st_ref_put(v_a_366_, v___x_533_);
v___y_494_ = v___y_509_;
v_a_495_ = v_a_514_;
goto v___jp_493_;
}
}
}
else
{
lean_dec(v___y_509_);
lean_dec_ref_known(v_x_365_, 2);
return v___x_513_;
}
}
else
{
lean_object* v_val_537_; 
v_val_537_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v___x_512_, 1);
v___y_494_ = v___y_509_;
v_a_495_ = v_val_537_;
goto v___jp_493_;
}
}
v___jp_538_:
{
uint8_t v___x_540_; 
v___x_540_ = l_Lean_Level_hasMVar(v_a_492_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; 
v___x_541_ = l_Lean_Level_hasParam(v_a_492_);
if (v___x_541_ == 0)
{
lean_inc(v_a_492_);
v___y_494_ = v_a_539_;
v_a_495_ = v_a_492_;
goto v___jp_493_;
}
else
{
v___y_509_ = v_a_539_;
goto v___jp_508_;
}
}
else
{
v___y_509_ = v_a_539_;
goto v___jp_508_;
}
}
v___jp_542_:
{
lean_object* v___x_543_; lean_object* v_visitedLevel_544_; lean_object* v___x_545_; 
v___x_543_ = lean_st_ref_get(v_a_366_);
v_visitedLevel_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc_ref(v_visitedLevel_544_);
lean_dec(v___x_543_);
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_544_, v_a_491_);
lean_dec_ref(v_visitedLevel_544_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v___x_546_; 
lean_inc(v_a_491_);
v___x_546_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_491_, v_a_366_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_548_; lean_object* v_visitedLevel_549_; lean_object* v_visitedExpr_550_; lean_object* v_levelParams_551_; lean_object* v_nextLevelIdx_552_; lean_object* v_levelArgs_553_; lean_object* v_newLocalDecls_554_; lean_object* v_newLocalDeclsForMVars_555_; lean_object* v_newLetDecls_556_; lean_object* v_nextExprIdx_557_; lean_object* v_exprMVarArgs_558_; lean_object* v_exprFVarArgs_559_; lean_object* v_toProcess_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_569_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = lean_st_ref_take(v_a_366_);
v_visitedLevel_549_ = lean_ctor_get(v___x_548_, 0);
v_visitedExpr_550_ = lean_ctor_get(v___x_548_, 1);
v_levelParams_551_ = lean_ctor_get(v___x_548_, 2);
v_nextLevelIdx_552_ = lean_ctor_get(v___x_548_, 3);
v_levelArgs_553_ = lean_ctor_get(v___x_548_, 4);
v_newLocalDecls_554_ = lean_ctor_get(v___x_548_, 5);
v_newLocalDeclsForMVars_555_ = lean_ctor_get(v___x_548_, 6);
v_newLetDecls_556_ = lean_ctor_get(v___x_548_, 7);
v_nextExprIdx_557_ = lean_ctor_get(v___x_548_, 8);
v_exprMVarArgs_558_ = lean_ctor_get(v___x_548_, 9);
v_exprFVarArgs_559_ = lean_ctor_get(v___x_548_, 10);
v_toProcess_560_ = lean_ctor_get(v___x_548_, 11);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_569_ == 0)
{
v___x_562_ = v___x_548_;
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_toProcess_560_);
lean_inc(v_exprFVarArgs_559_);
lean_inc(v_exprMVarArgs_558_);
lean_inc(v_nextExprIdx_557_);
lean_inc(v_newLetDecls_556_);
lean_inc(v_newLocalDeclsForMVars_555_);
lean_inc(v_newLocalDecls_554_);
lean_inc(v_levelArgs_553_);
lean_inc(v_nextLevelIdx_552_);
lean_inc(v_levelParams_551_);
lean_inc(v_visitedExpr_550_);
lean_inc(v_visitedLevel_549_);
lean_dec(v___x_548_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_566_; 
lean_inc(v_a_547_);
lean_inc(v_a_491_);
v___x_564_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_549_, v_a_491_, v_a_547_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_566_ = v___x_562_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_visitedExpr_550_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_levelParams_551_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_nextLevelIdx_552_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_levelArgs_553_);
lean_ctor_set(v_reuseFailAlloc_568_, 5, v_newLocalDecls_554_);
lean_ctor_set(v_reuseFailAlloc_568_, 6, v_newLocalDeclsForMVars_555_);
lean_ctor_set(v_reuseFailAlloc_568_, 7, v_newLetDecls_556_);
lean_ctor_set(v_reuseFailAlloc_568_, 8, v_nextExprIdx_557_);
lean_ctor_set(v_reuseFailAlloc_568_, 9, v_exprMVarArgs_558_);
lean_ctor_set(v_reuseFailAlloc_568_, 10, v_exprFVarArgs_559_);
lean_ctor_set(v_reuseFailAlloc_568_, 11, v_toProcess_560_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; 
v___x_567_ = lean_st_ref_put(v_a_366_, v___x_566_);
v_a_539_ = v_a_547_;
goto v___jp_538_;
}
}
}
else
{
lean_dec_ref_known(v_x_365_, 2);
return v___x_546_;
}
}
else
{
lean_object* v_val_570_; 
v_val_570_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_570_);
lean_dec_ref_known(v___x_545_, 1);
v_a_539_ = v_val_570_;
goto v___jp_538_;
}
}
}
default: 
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_x_365_, v_a_366_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object* v_x_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_574_, v_a_575_);
lean_dec(v_a_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* v_x_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_578_, v_a_580_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* v_x_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Meta_Closure_collectLevelAux(v_x_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(lean_object* v_00_u03b2_596_, lean_object* v_m_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_597_, v_a_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object* v_00_u03b2_600_, lean_object* v_m_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(v_00_u03b2_600_, v_m_601_, v_a_602_);
lean_dec(v_a_602_);
lean_dec_ref(v_m_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2(lean_object* v_00_u03b2_604_, lean_object* v_m_605_, lean_object* v_a_606_, lean_object* v_b_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_m_605_, v_a_606_, v_b_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(lean_object* v_00_u03b2_609_, lean_object* v_a_610_, lean_object* v_x_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_610_, v_x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___boxed(lean_object* v_00_u03b2_613_, lean_object* v_a_614_, lean_object* v_x_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(v_00_u03b2_613_, v_a_614_, v_x_615_);
lean_dec(v_x_615_);
lean_dec(v_a_614_);
return v_res_616_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(lean_object* v_00_u03b2_617_, lean_object* v_a_618_, lean_object* v_x_619_){
_start:
{
uint8_t v___x_620_; 
v___x_620_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_618_, v_x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___boxed(lean_object* v_00_u03b2_621_, lean_object* v_a_622_, lean_object* v_x_623_){
_start:
{
uint8_t v_res_624_; lean_object* v_r_625_; 
v_res_624_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(v_00_u03b2_621_, v_a_622_, v_x_623_);
lean_dec(v_x_623_);
lean_dec(v_a_622_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4(lean_object* v_00_u03b2_626_, lean_object* v_data_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_data_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5(lean_object* v_00_u03b2_629_, lean_object* v_a_630_, lean_object* v_b_631_, lean_object* v_x_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_630_, v_b_631_, v_x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_634_, lean_object* v_i_635_, lean_object* v_source_636_, lean_object* v_target_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v_i_635_, v_source_636_, v_target_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_639_, lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_x_640_, v_x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object* v_u_643_, lean_object* v_a_644_){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = l_Lean_Level_hasMVar(v_u_643_);
if (v___x_689_ == 0)
{
uint8_t v___x_690_; 
v___x_690_ = l_Lean_Level_hasParam(v_u_643_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v_u_643_);
return v___x_691_;
}
else
{
goto v___jp_646_;
}
}
else
{
goto v___jp_646_;
}
v___jp_646_:
{
lean_object* v___x_647_; lean_object* v_visitedLevel_648_; lean_object* v___x_649_; 
v___x_647_ = lean_st_ref_get(v_a_644_);
v_visitedLevel_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_visitedLevel_648_);
lean_dec(v___x_647_);
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_648_, v_u_643_);
lean_dec_ref(v_visitedLevel_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_650_; 
lean_inc(v_u_643_);
v___x_650_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_u_643_, v_a_644_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_680_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_680_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_680_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_680_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v_visitedLevel_656_; lean_object* v_visitedExpr_657_; lean_object* v_levelParams_658_; lean_object* v_nextLevelIdx_659_; lean_object* v_levelArgs_660_; lean_object* v_newLocalDecls_661_; lean_object* v_newLocalDeclsForMVars_662_; lean_object* v_newLetDecls_663_; lean_object* v_nextExprIdx_664_; lean_object* v_exprMVarArgs_665_; lean_object* v_exprFVarArgs_666_; lean_object* v_toProcess_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_679_; 
v___x_655_ = lean_st_ref_take(v_a_644_);
v_visitedLevel_656_ = lean_ctor_get(v___x_655_, 0);
v_visitedExpr_657_ = lean_ctor_get(v___x_655_, 1);
v_levelParams_658_ = lean_ctor_get(v___x_655_, 2);
v_nextLevelIdx_659_ = lean_ctor_get(v___x_655_, 3);
v_levelArgs_660_ = lean_ctor_get(v___x_655_, 4);
v_newLocalDecls_661_ = lean_ctor_get(v___x_655_, 5);
v_newLocalDeclsForMVars_662_ = lean_ctor_get(v___x_655_, 6);
v_newLetDecls_663_ = lean_ctor_get(v___x_655_, 7);
v_nextExprIdx_664_ = lean_ctor_get(v___x_655_, 8);
v_exprMVarArgs_665_ = lean_ctor_get(v___x_655_, 9);
v_exprFVarArgs_666_ = lean_ctor_get(v___x_655_, 10);
v_toProcess_667_ = lean_ctor_get(v___x_655_, 11);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_679_ == 0)
{
v___x_669_ = v___x_655_;
v_isShared_670_ = v_isSharedCheck_679_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_toProcess_667_);
lean_inc(v_exprFVarArgs_666_);
lean_inc(v_exprMVarArgs_665_);
lean_inc(v_nextExprIdx_664_);
lean_inc(v_newLetDecls_663_);
lean_inc(v_newLocalDeclsForMVars_662_);
lean_inc(v_newLocalDecls_661_);
lean_inc(v_levelArgs_660_);
lean_inc(v_nextLevelIdx_659_);
lean_inc(v_levelParams_658_);
lean_inc(v_visitedExpr_657_);
lean_inc(v_visitedLevel_656_);
lean_dec(v___x_655_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_679_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
lean_inc(v_a_651_);
v___x_671_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_656_, v_u_643_, v_a_651_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_visitedExpr_657_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_levelParams_658_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_nextLevelIdx_659_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v_levelArgs_660_);
lean_ctor_set(v_reuseFailAlloc_678_, 5, v_newLocalDecls_661_);
lean_ctor_set(v_reuseFailAlloc_678_, 6, v_newLocalDeclsForMVars_662_);
lean_ctor_set(v_reuseFailAlloc_678_, 7, v_newLetDecls_663_);
lean_ctor_set(v_reuseFailAlloc_678_, 8, v_nextExprIdx_664_);
lean_ctor_set(v_reuseFailAlloc_678_, 9, v_exprMVarArgs_665_);
lean_ctor_set(v_reuseFailAlloc_678_, 10, v_exprFVarArgs_666_);
lean_ctor_set(v_reuseFailAlloc_678_, 11, v_toProcess_667_);
v___x_673_ = v_reuseFailAlloc_678_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_st_ref_put(v_a_644_, v___x_673_);
if (v_isShared_654_ == 0)
{
v___x_676_ = v___x_653_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_651_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
else
{
lean_dec(v_u_643_);
return v___x_650_;
}
}
else
{
lean_object* v_val_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec(v_u_643_);
v_val_681_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_649_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_val_681_);
lean_dec(v___x_649_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set_tag(v___x_683_, 0);
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_val_681_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg___boxed(lean_object* v_u_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_692_, v_a_693_);
lean_dec(v_a_693_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* v_u_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_696_, v_a_698_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* v_u_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Meta_Closure_collectLevel(v_u_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object* v_e_714_, lean_object* v___y_715_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_Expr_hasMVar(v_e_714_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v_e_714_);
return v___x_718_;
}
else
{
lean_object* v___x_719_; lean_object* v_mctx_720_; lean_object* v___x_721_; lean_object* v_fst_722_; lean_object* v_snd_723_; lean_object* v___x_724_; lean_object* v_cache_725_; lean_object* v_zetaDeltaFVarIds_726_; lean_object* v_postponed_727_; lean_object* v_diag_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_737_; 
v___x_719_ = lean_st_ref_get(v___y_715_);
v_mctx_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc_ref(v_mctx_720_);
lean_dec(v___x_719_);
v___x_721_ = l_Lean_instantiateMVarsCore(v_mctx_720_, v_e_714_);
v_fst_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_fst_722_);
v_snd_723_ = lean_ctor_get(v___x_721_, 1);
lean_inc(v_snd_723_);
lean_dec_ref(v___x_721_);
v___x_724_ = lean_st_ref_take(v___y_715_);
v_cache_725_ = lean_ctor_get(v___x_724_, 1);
v_zetaDeltaFVarIds_726_ = lean_ctor_get(v___x_724_, 2);
v_postponed_727_ = lean_ctor_get(v___x_724_, 3);
v_diag_728_ = lean_ctor_get(v___x_724_, 4);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v___x_724_, 0);
lean_dec(v_unused_738_);
v___x_730_ = v___x_724_;
v_isShared_731_ = v_isSharedCheck_737_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_diag_728_);
lean_inc(v_postponed_727_);
lean_inc(v_zetaDeltaFVarIds_726_);
lean_inc(v_cache_725_);
lean_dec(v___x_724_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_737_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v_snd_723_);
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_snd_723_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_cache_725_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v_zetaDeltaFVarIds_726_);
lean_ctor_set(v_reuseFailAlloc_736_, 3, v_postponed_727_);
lean_ctor_set(v_reuseFailAlloc_736_, 4, v_diag_728_);
v___x_733_ = v_reuseFailAlloc_736_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_st_ref_put(v___y_715_, v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v_fst_722_);
return v___x_735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object* v_e_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_739_, v___y_740_);
lean_dec(v___y_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(lean_object* v_e_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_743_, v___y_747_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object* v_e_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(v_e_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object* v_e_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_769_; uint8_t v_zetaDelta_770_; 
v___x_769_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_761_, v_a_765_);
v_zetaDelta_770_ = lean_ctor_get_uint8(v_a_762_, 0);
if (v_zetaDelta_770_ == 0)
{
uint8_t v_hasLetDecls_771_; 
v_hasLetDecls_771_ = lean_ctor_get_uint8(v_a_762_, 1);
if (v_hasLetDecls_771_ == 0)
{
return v___x_769_;
}
else
{
lean_object* v_a_772_; uint8_t v___x_773_; lean_object* v___x_774_; 
v_a_772_ = lean_ctor_get(v___x_769_, 0);
lean_inc_n(v_a_772_, 2);
lean_dec_ref(v___x_769_);
v___x_773_ = 0;
v___x_774_ = l_Lean_Meta_check(v_a_772_, v___x_773_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v___x_774_, 0);
lean_dec(v_unused_782_);
v___x_776_ = v___x_774_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_dec(v___x_774_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v_a_772_);
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_772_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_a_772_);
v_a_783_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_774_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_774_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
else
{
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* v_e_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Meta_Closure_preprocess(v_e_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object* v_a_803_){
_start:
{
lean_object* v___x_805_; lean_object* v_nextExprIdx_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_visitedLevel_810_; lean_object* v_visitedExpr_811_; lean_object* v_levelParams_812_; lean_object* v_nextLevelIdx_813_; lean_object* v_levelArgs_814_; lean_object* v_newLocalDecls_815_; lean_object* v_newLocalDeclsForMVars_816_; lean_object* v_newLetDecls_817_; lean_object* v_nextExprIdx_818_; lean_object* v_exprMVarArgs_819_; lean_object* v_exprFVarArgs_820_; lean_object* v_toProcess_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_832_; 
v___x_805_ = lean_st_ref_get(v_a_803_);
v_nextExprIdx_806_ = lean_ctor_get(v___x_805_, 8);
lean_inc(v_nextExprIdx_806_);
lean_dec(v___x_805_);
v___x_807_ = ((lean_object*)(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1));
v___x_808_ = lean_name_append_index_after(v___x_807_, v_nextExprIdx_806_);
v___x_809_ = lean_st_ref_take(v_a_803_);
v_visitedLevel_810_ = lean_ctor_get(v___x_809_, 0);
v_visitedExpr_811_ = lean_ctor_get(v___x_809_, 1);
v_levelParams_812_ = lean_ctor_get(v___x_809_, 2);
v_nextLevelIdx_813_ = lean_ctor_get(v___x_809_, 3);
v_levelArgs_814_ = lean_ctor_get(v___x_809_, 4);
v_newLocalDecls_815_ = lean_ctor_get(v___x_809_, 5);
v_newLocalDeclsForMVars_816_ = lean_ctor_get(v___x_809_, 6);
v_newLetDecls_817_ = lean_ctor_get(v___x_809_, 7);
v_nextExprIdx_818_ = lean_ctor_get(v___x_809_, 8);
v_exprMVarArgs_819_ = lean_ctor_get(v___x_809_, 9);
v_exprFVarArgs_820_ = lean_ctor_get(v___x_809_, 10);
v_toProcess_821_ = lean_ctor_get(v___x_809_, 11);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_832_ == 0)
{
v___x_823_ = v___x_809_;
v_isShared_824_ = v_isSharedCheck_832_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_toProcess_821_);
lean_inc(v_exprFVarArgs_820_);
lean_inc(v_exprMVarArgs_819_);
lean_inc(v_nextExprIdx_818_);
lean_inc(v_newLetDecls_817_);
lean_inc(v_newLocalDeclsForMVars_816_);
lean_inc(v_newLocalDecls_815_);
lean_inc(v_levelArgs_814_);
lean_inc(v_nextLevelIdx_813_);
lean_inc(v_levelParams_812_);
lean_inc(v_visitedExpr_811_);
lean_inc(v_visitedLevel_810_);
lean_dec(v___x_809_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_832_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = lean_nat_add(v_nextExprIdx_818_, v___x_825_);
lean_dec(v_nextExprIdx_818_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 8, v___x_826_);
v___x_828_ = v___x_823_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_visitedLevel_810_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_visitedExpr_811_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_levelParams_812_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v_nextLevelIdx_813_);
lean_ctor_set(v_reuseFailAlloc_831_, 4, v_levelArgs_814_);
lean_ctor_set(v_reuseFailAlloc_831_, 5, v_newLocalDecls_815_);
lean_ctor_set(v_reuseFailAlloc_831_, 6, v_newLocalDeclsForMVars_816_);
lean_ctor_set(v_reuseFailAlloc_831_, 7, v_newLetDecls_817_);
lean_ctor_set(v_reuseFailAlloc_831_, 8, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_831_, 9, v_exprMVarArgs_819_);
lean_ctor_set(v_reuseFailAlloc_831_, 10, v_exprFVarArgs_820_);
lean_ctor_set(v_reuseFailAlloc_831_, 11, v_toProcess_821_);
v___x_828_ = v_reuseFailAlloc_831_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_st_ref_put(v_a_803_, v___x_828_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_808_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_833_);
lean_dec(v_a_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_837_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Meta_Closure_mkNextUserName(v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object* v_elem_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_855_; lean_object* v_visitedLevel_856_; lean_object* v_visitedExpr_857_; lean_object* v_levelParams_858_; lean_object* v_nextLevelIdx_859_; lean_object* v_levelArgs_860_; lean_object* v_newLocalDecls_861_; lean_object* v_newLocalDeclsForMVars_862_; lean_object* v_newLetDecls_863_; lean_object* v_nextExprIdx_864_; lean_object* v_exprMVarArgs_865_; lean_object* v_exprFVarArgs_866_; lean_object* v_toProcess_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_878_; 
v___x_855_ = lean_st_ref_take(v_a_853_);
v_visitedLevel_856_ = lean_ctor_get(v___x_855_, 0);
v_visitedExpr_857_ = lean_ctor_get(v___x_855_, 1);
v_levelParams_858_ = lean_ctor_get(v___x_855_, 2);
v_nextLevelIdx_859_ = lean_ctor_get(v___x_855_, 3);
v_levelArgs_860_ = lean_ctor_get(v___x_855_, 4);
v_newLocalDecls_861_ = lean_ctor_get(v___x_855_, 5);
v_newLocalDeclsForMVars_862_ = lean_ctor_get(v___x_855_, 6);
v_newLetDecls_863_ = lean_ctor_get(v___x_855_, 7);
v_nextExprIdx_864_ = lean_ctor_get(v___x_855_, 8);
v_exprMVarArgs_865_ = lean_ctor_get(v___x_855_, 9);
v_exprFVarArgs_866_ = lean_ctor_get(v___x_855_, 10);
v_toProcess_867_ = lean_ctor_get(v___x_855_, 11);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_878_ == 0)
{
v___x_869_ = v___x_855_;
v_isShared_870_ = v_isSharedCheck_878_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_toProcess_867_);
lean_inc(v_exprFVarArgs_866_);
lean_inc(v_exprMVarArgs_865_);
lean_inc(v_nextExprIdx_864_);
lean_inc(v_newLetDecls_863_);
lean_inc(v_newLocalDeclsForMVars_862_);
lean_inc(v_newLocalDecls_861_);
lean_inc(v_levelArgs_860_);
lean_inc(v_nextLevelIdx_859_);
lean_inc(v_levelParams_858_);
lean_inc(v_visitedExpr_857_);
lean_inc(v_visitedLevel_856_);
lean_dec(v___x_855_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_878_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_871_ = lean_box(0);
v___x_872_ = lean_array_push(v_toProcess_867_, v_elem_852_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 11, v___x_872_);
v___x_874_ = v___x_869_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_visitedLevel_856_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_visitedExpr_857_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_levelParams_858_);
lean_ctor_set(v_reuseFailAlloc_877_, 3, v_nextLevelIdx_859_);
lean_ctor_set(v_reuseFailAlloc_877_, 4, v_levelArgs_860_);
lean_ctor_set(v_reuseFailAlloc_877_, 5, v_newLocalDecls_861_);
lean_ctor_set(v_reuseFailAlloc_877_, 6, v_newLocalDeclsForMVars_862_);
lean_ctor_set(v_reuseFailAlloc_877_, 7, v_newLetDecls_863_);
lean_ctor_set(v_reuseFailAlloc_877_, 8, v_nextExprIdx_864_);
lean_ctor_set(v_reuseFailAlloc_877_, 9, v_exprMVarArgs_865_);
lean_ctor_set(v_reuseFailAlloc_877_, 10, v_exprFVarArgs_866_);
lean_ctor_set(v_reuseFailAlloc_877_, 11, v___x_872_);
v___x_874_ = v_reuseFailAlloc_877_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_st_ref_put(v_a_853_, v___x_874_);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_871_);
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object* v_elem_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_879_, v_a_880_);
lean_dec(v_a_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* v_elem_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_883_, v_a_885_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* v_elem_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Meta_Closure_pushToProcess(v_elem_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(lean_object* v_mvarId_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; lean_object* v_mctx_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_904_ = lean_st_ref_get(v___y_902_);
v_mctx_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc_ref(v_mctx_905_);
lean_dec(v___x_904_);
v___x_906_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_905_, v_mvarId_901_);
lean_dec_ref(v_mctx_905_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(lean_object* v_mvarId_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec(v_mvarId_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(lean_object* v_mvarId_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_912_, v___y_916_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object* v_mvarId_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(v_mvarId_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v_mvarId_921_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(lean_object* v_k_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v_b_933_, lean_object* v_c_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; 
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_932_);
lean_inc_ref(v___y_931_);
v___x_940_ = lean_apply_9(v_k_930_, v_b_933_, v_c_934_, v___y_931_, v___y_932_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, lean_box(0));
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed(lean_object* v_k_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v_b_944_, lean_object* v_c_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(v_k_941_, v___y_942_, v___y_943_, v_b_944_, v_c_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object* v_type_952_, lean_object* v_maxFVars_x3f_953_, lean_object* v_k_954_, uint8_t v_cleanupAnnotations_955_, uint8_t v_whnfType_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___f_964_; lean_object* v___x_965_; 
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
v___f_964_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_964_, 0, v_k_954_);
lean_closure_set(v___f_964_, 1, v___y_957_);
lean_closure_set(v___f_964_, 2, v___y_958_);
v___x_965_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_952_, v_maxFVars_x3f_953_, v___f_964_, v_cleanupAnnotations_955_, v_whnfType_956_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
if (lean_obj_tag(v___x_965_) == 0)
{
return v___x_965_;
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(lean_object* v_type_974_, lean_object* v_maxFVars_x3f_975_, lean_object* v_k_976_, lean_object* v_cleanupAnnotations_977_, lean_object* v_whnfType_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_986_; uint8_t v_whnfType_boxed_987_; lean_object* v_res_988_; 
v_cleanupAnnotations_boxed_986_ = lean_unbox(v_cleanupAnnotations_977_);
v_whnfType_boxed_987_ = lean_unbox(v_whnfType_978_);
v_res_988_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_974_, v_maxFVars_x3f_975_, v_k_976_, v_cleanupAnnotations_boxed_986_, v_whnfType_boxed_987_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_object* v_00_u03b1_989_, lean_object* v_type_990_, lean_object* v_maxFVars_x3f_991_, lean_object* v_k_992_, uint8_t v_cleanupAnnotations_993_, uint8_t v_whnfType_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_990_, v_maxFVars_x3f_991_, v_k_992_, v_cleanupAnnotations_993_, v_whnfType_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(lean_object* v_00_u03b1_1003_, lean_object* v_type_1004_, lean_object* v_maxFVars_x3f_1005_, lean_object* v_k_1006_, lean_object* v_cleanupAnnotations_1007_, lean_object* v_whnfType_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1016_; uint8_t v_whnfType_boxed_1017_; lean_object* v_res_1018_; 
v_cleanupAnnotations_boxed_1016_ = lean_unbox(v_cleanupAnnotations_1007_);
v_whnfType_boxed_1017_ = lean_unbox(v_whnfType_1008_);
v_res_1018_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(v_00_u03b1_1003_, v_type_1004_, v_maxFVars_x3f_1005_, v_k_1006_, v_cleanupAnnotations_boxed_1016_, v_whnfType_boxed_1017_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object* v_a_1019_, lean_object* v_x_1020_){
_start:
{
if (lean_obj_tag(v_x_1020_) == 0)
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_box(0);
return v___x_1021_;
}
else
{
lean_object* v_key_1022_; lean_object* v_value_1023_; lean_object* v_tail_1024_; uint8_t v___x_1025_; 
v_key_1022_ = lean_ctor_get(v_x_1020_, 0);
v_value_1023_ = lean_ctor_get(v_x_1020_, 1);
v_tail_1024_ = lean_ctor_get(v_x_1020_, 2);
v___x_1025_ = l_Lean_ExprStructEq_beq(v_key_1022_, v_a_1019_);
if (v___x_1025_ == 0)
{
v_x_1020_ = v_tail_1024_;
goto _start;
}
else
{
lean_object* v___x_1027_; 
lean_inc(v_value_1023_);
v___x_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_value_1023_);
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1028_, v_x_1029_);
lean_dec(v_x_1029_);
lean_dec_ref(v_a_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object* v_m_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_buckets_1033_; lean_object* v___x_1034_; uint64_t v___x_1035_; uint64_t v___x_1036_; uint64_t v___x_1037_; uint64_t v_fold_1038_; uint64_t v___x_1039_; uint64_t v___x_1040_; uint64_t v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v_buckets_1033_ = lean_ctor_get(v_m_1031_, 1);
v___x_1034_ = lean_array_get_size(v_buckets_1033_);
v___x_1035_ = l_Lean_ExprStructEq_hash(v_a_1032_);
v___x_1036_ = 32ULL;
v___x_1037_ = lean_uint64_shift_right(v___x_1035_, v___x_1036_);
v_fold_1038_ = lean_uint64_xor(v___x_1035_, v___x_1037_);
v___x_1039_ = 16ULL;
v___x_1040_ = lean_uint64_shift_right(v_fold_1038_, v___x_1039_);
v___x_1041_ = lean_uint64_xor(v_fold_1038_, v___x_1040_);
v___x_1042_ = lean_uint64_to_usize(v___x_1041_);
v___x_1043_ = lean_usize_of_nat(v___x_1034_);
v___x_1044_ = ((size_t)1ULL);
v___x_1045_ = lean_usize_sub(v___x_1043_, v___x_1044_);
v___x_1046_ = lean_usize_land(v___x_1042_, v___x_1045_);
v___x_1047_ = lean_array_uget_borrowed(v_buckets_1033_, v___x_1046_);
v___x_1048_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1032_, v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object* v_m_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1049_, v_a_1050_);
lean_dec_ref(v_a_1050_);
lean_dec_ref(v_m_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v___y_1054_){
_start:
{
if (lean_obj_tag(v_x_1052_) == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = l_List_reverse___redArg(v_x_1053_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
else
{
lean_object* v_head_1058_; lean_object* v_tail_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1077_; 
v_head_1058_ = lean_ctor_get(v_x_1052_, 0);
v_tail_1059_ = lean_ctor_get(v_x_1052_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_x_1052_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1061_ = v_x_1052_;
v_isShared_1062_ = v_isSharedCheck_1077_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_tail_1059_);
lean_inc(v_head_1058_);
lean_dec(v_x_1052_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1077_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Meta_Closure_collectLevel___redArg(v_head_1058_, v___y_1054_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v_x_1053_);
lean_ctor_set(v___x_1061_, 0, v_a_1064_);
v___x_1066_ = v___x_1061_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1064_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_x_1053_);
v___x_1066_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
v_x_1052_ = v_tail_1059_;
v_x_1053_ = v___x_1066_;
goto _start;
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_del_object(v___x_1061_);
lean_dec(v_tail_1059_);
lean_dec(v_x_1053_);
v_a_1069_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1063_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1063_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1078_, v_x_1079_, v___y_1080_);
lean_dec(v___y_1080_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; lean_object* v_ngen_1086_; lean_object* v_namePrefix_1087_; lean_object* v_idx_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1118_; 
v___x_1085_ = lean_st_ref_get(v___y_1083_);
v_ngen_1086_ = lean_ctor_get(v___x_1085_, 2);
lean_inc_ref(v_ngen_1086_);
lean_dec(v___x_1085_);
v_namePrefix_1087_ = lean_ctor_get(v_ngen_1086_, 0);
v_idx_1088_ = lean_ctor_get(v_ngen_1086_, 1);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_ngen_1086_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1090_ = v_ngen_1086_;
v_isShared_1091_ = v_isSharedCheck_1118_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_idx_1088_);
lean_inc(v_namePrefix_1087_);
lean_dec(v_ngen_1086_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1118_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_r_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
lean_inc(v_idx_1088_);
lean_inc(v_namePrefix_1087_);
v_r_1092_ = l_Lean_Name_num___override(v_namePrefix_1087_, v_idx_1088_);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_add(v_idx_1088_, v___x_1093_);
lean_dec(v_idx_1088_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v___x_1094_);
v___x_1096_ = v___x_1090_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_namePrefix_1087_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; lean_object* v_env_1098_; lean_object* v_nextMacroScope_1099_; lean_object* v_auxDeclNGen_1100_; lean_object* v_traceState_1101_; lean_object* v_cache_1102_; lean_object* v_recordedDeps_1103_; lean_object* v_messages_1104_; lean_object* v_infoState_1105_; lean_object* v_snapshotTasks_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1115_; 
v___x_1097_ = lean_st_ref_take(v___y_1083_);
v_env_1098_ = lean_ctor_get(v___x_1097_, 0);
v_nextMacroScope_1099_ = lean_ctor_get(v___x_1097_, 1);
v_auxDeclNGen_1100_ = lean_ctor_get(v___x_1097_, 3);
v_traceState_1101_ = lean_ctor_get(v___x_1097_, 4);
v_cache_1102_ = lean_ctor_get(v___x_1097_, 5);
v_recordedDeps_1103_ = lean_ctor_get(v___x_1097_, 6);
v_messages_1104_ = lean_ctor_get(v___x_1097_, 7);
v_infoState_1105_ = lean_ctor_get(v___x_1097_, 8);
v_snapshotTasks_1106_ = lean_ctor_get(v___x_1097_, 9);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v___x_1097_, 2);
lean_dec(v_unused_1116_);
v___x_1108_ = v___x_1097_;
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_snapshotTasks_1106_);
lean_inc(v_infoState_1105_);
lean_inc(v_messages_1104_);
lean_inc(v_recordedDeps_1103_);
lean_inc(v_cache_1102_);
lean_inc(v_traceState_1101_);
lean_inc(v_auxDeclNGen_1100_);
lean_inc(v_nextMacroScope_1099_);
lean_inc(v_env_1098_);
lean_dec(v___x_1097_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 2, v___x_1096_);
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_env_1098_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_nextMacroScope_1099_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_auxDeclNGen_1100_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_traceState_1101_);
lean_ctor_set(v_reuseFailAlloc_1114_, 5, v_cache_1102_);
lean_ctor_set(v_reuseFailAlloc_1114_, 6, v_recordedDeps_1103_);
lean_ctor_set(v_reuseFailAlloc_1114_, 7, v_messages_1104_);
lean_ctor_set(v_reuseFailAlloc_1114_, 8, v_infoState_1105_);
lean_ctor_set(v_reuseFailAlloc_1114_, 9, v_snapshotTasks_1106_);
v___x_1111_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_st_ref_put(v___y_1083_, v___x_1111_);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_r_1092_);
return v___x_1113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg___boxed(lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1119_);
lean_dec(v___y_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v___x_1129_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1127_);
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object* v_e_1146_, lean_object* v_args_1147_, lean_object* v_x_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; uint8_t v___x_1157_; uint8_t v___x_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; 
v___x_1156_ = l_Lean_mkAppN(v_e_1146_, v_args_1147_);
v___x_1157_ = 0;
v___x_1158_ = 1;
v___x_1159_ = 1;
v___x_1160_ = l_Lean_Meta_mkLambdaFVars(v_args_1147_, v___x_1156_, v___x_1157_, v___x_1158_, v___x_1157_, v___x_1158_, v___x_1159_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object* v_e_1161_, lean_object* v_args_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Meta_Closure_collectExprAux___lam__1(v_e_1161_, v_args_1162_, v_x_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec_ref(v_x_1163_);
lean_dec_ref(v_args_1162_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_x_1172_, lean_object* v_x_1173_){
_start:
{
if (lean_obj_tag(v_x_1173_) == 0)
{
return v_x_1172_;
}
else
{
lean_object* v_key_1174_; lean_object* v_value_1175_; lean_object* v_tail_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1199_; 
v_key_1174_ = lean_ctor_get(v_x_1173_, 0);
v_value_1175_ = lean_ctor_get(v_x_1173_, 1);
v_tail_1176_ = lean_ctor_get(v_x_1173_, 2);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_x_1173_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1178_ = v_x_1173_;
v_isShared_1179_ = v_isSharedCheck_1199_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_tail_1176_);
lean_inc(v_value_1175_);
lean_inc(v_key_1174_);
lean_dec(v_x_1173_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1199_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; uint64_t v___x_1181_; uint64_t v___x_1182_; uint64_t v___x_1183_; uint64_t v_fold_1184_; uint64_t v___x_1185_; uint64_t v___x_1186_; uint64_t v___x_1187_; size_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; size_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1180_ = lean_array_get_size(v_x_1172_);
v___x_1181_ = l_Lean_ExprStructEq_hash(v_key_1174_);
v___x_1182_ = 32ULL;
v___x_1183_ = lean_uint64_shift_right(v___x_1181_, v___x_1182_);
v_fold_1184_ = lean_uint64_xor(v___x_1181_, v___x_1183_);
v___x_1185_ = 16ULL;
v___x_1186_ = lean_uint64_shift_right(v_fold_1184_, v___x_1185_);
v___x_1187_ = lean_uint64_xor(v_fold_1184_, v___x_1186_);
v___x_1188_ = lean_uint64_to_usize(v___x_1187_);
v___x_1189_ = lean_usize_of_nat(v___x_1180_);
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_sub(v___x_1189_, v___x_1190_);
v___x_1192_ = lean_usize_land(v___x_1188_, v___x_1191_);
v___x_1193_ = lean_array_uget_borrowed(v_x_1172_, v___x_1192_);
lean_inc(v___x_1193_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 2, v___x_1193_);
v___x_1195_ = v___x_1178_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_key_1174_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_value_1175_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_array_uset(v_x_1172_, v___x_1192_, v___x_1195_);
v_x_1172_ = v___x_1196_;
v_x_1173_ = v_tail_1176_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(lean_object* v_i_1200_, lean_object* v_source_1201_, lean_object* v_target_1202_){
_start:
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = lean_array_get_size(v_source_1201_);
v___x_1204_ = lean_nat_dec_lt(v_i_1200_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_dec_ref(v_source_1201_);
lean_dec(v_i_1200_);
return v_target_1202_;
}
else
{
lean_object* v_es_1205_; lean_object* v___x_1206_; lean_object* v_source_1207_; lean_object* v_target_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_es_1205_ = lean_array_fget(v_source_1201_, v_i_1200_);
v___x_1206_ = lean_box(0);
v_source_1207_ = lean_array_fset(v_source_1201_, v_i_1200_, v___x_1206_);
v_target_1208_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_target_1202_, v_es_1205_);
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = lean_nat_add(v_i_1200_, v___x_1209_);
lean_dec(v_i_1200_);
v_i_1200_ = v___x_1210_;
v_source_1201_ = v_source_1207_;
v_target_1202_ = v_target_1208_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(lean_object* v_data_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_nbuckets_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1213_ = lean_array_get_size(v_data_1212_);
v___x_1214_ = lean_unsigned_to_nat(2u);
v_nbuckets_1215_ = lean_nat_mul(v___x_1213_, v___x_1214_);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_box(0);
v___x_1218_ = lean_mk_array(v_nbuckets_1215_, v___x_1217_);
v___x_1219_ = lean_array_propagate_mark(v_data_1212_, v___x_1218_);
v___x_1220_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v___x_1216_, v_data_1212_, v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(lean_object* v_a_1221_, lean_object* v_b_1222_, lean_object* v_x_1223_){
_start:
{
if (lean_obj_tag(v_x_1223_) == 0)
{
lean_dec(v_b_1222_);
lean_dec_ref(v_a_1221_);
return v_x_1223_;
}
else
{
lean_object* v_key_1224_; lean_object* v_value_1225_; lean_object* v_tail_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1238_; 
v_key_1224_ = lean_ctor_get(v_x_1223_, 0);
v_value_1225_ = lean_ctor_get(v_x_1223_, 1);
v_tail_1226_ = lean_ctor_get(v_x_1223_, 2);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_x_1223_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1228_ = v_x_1223_;
v_isShared_1229_ = v_isSharedCheck_1238_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_tail_1226_);
lean_inc(v_value_1225_);
lean_inc(v_key_1224_);
lean_dec(v_x_1223_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1238_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
uint8_t v___x_1230_; 
v___x_1230_ = l_Lean_ExprStructEq_beq(v_key_1224_, v_a_1221_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1221_, v_b_1222_, v_tail_1226_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 2, v___x_1231_);
v___x_1233_ = v___x_1228_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_key_1224_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_value_1225_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
else
{
lean_object* v___x_1236_; 
lean_dec(v_value_1225_);
lean_dec(v_key_1224_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v_b_1222_);
lean_ctor_set(v___x_1228_, 0, v_a_1221_);
v___x_1236_ = v___x_1228_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1221_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_b_1222_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_tail_1226_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object* v_a_1239_, lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 0)
{
uint8_t v___x_1241_; 
v___x_1241_ = 0;
return v___x_1241_;
}
else
{
lean_object* v_key_1242_; lean_object* v_tail_1243_; uint8_t v___x_1244_; 
v_key_1242_ = lean_ctor_get(v_x_1240_, 0);
v_tail_1243_ = lean_ctor_get(v_x_1240_, 2);
v___x_1244_ = l_Lean_ExprStructEq_beq(v_key_1242_, v_a_1239_);
if (v___x_1244_ == 0)
{
v_x_1240_ = v_tail_1243_;
goto _start;
}
else
{
return v___x_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object* v_a_1246_, lean_object* v_x_1247_){
_start:
{
uint8_t v_res_1248_; lean_object* v_r_1249_; 
v_res_1248_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1246_, v_x_1247_);
lean_dec(v_x_1247_);
lean_dec_ref(v_a_1246_);
v_r_1249_ = lean_box(v_res_1248_);
return v_r_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object* v_m_1250_, lean_object* v_a_1251_, lean_object* v_b_1252_){
_start:
{
lean_object* v_size_1253_; lean_object* v_buckets_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1297_; 
v_size_1253_ = lean_ctor_get(v_m_1250_, 0);
v_buckets_1254_ = lean_ctor_get(v_m_1250_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_m_1250_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1256_ = v_m_1250_;
v_isShared_1257_ = v_isSharedCheck_1297_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_buckets_1254_);
lean_inc(v_size_1253_);
lean_dec(v_m_1250_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1297_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; uint64_t v___x_1259_; uint64_t v___x_1260_; uint64_t v___x_1261_; uint64_t v_fold_1262_; uint64_t v___x_1263_; uint64_t v___x_1264_; uint64_t v___x_1265_; size_t v___x_1266_; size_t v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; lean_object* v_bkt_1271_; uint8_t v___x_1272_; 
v___x_1258_ = lean_array_get_size(v_buckets_1254_);
v___x_1259_ = l_Lean_ExprStructEq_hash(v_a_1251_);
v___x_1260_ = 32ULL;
v___x_1261_ = lean_uint64_shift_right(v___x_1259_, v___x_1260_);
v_fold_1262_ = lean_uint64_xor(v___x_1259_, v___x_1261_);
v___x_1263_ = 16ULL;
v___x_1264_ = lean_uint64_shift_right(v_fold_1262_, v___x_1263_);
v___x_1265_ = lean_uint64_xor(v_fold_1262_, v___x_1264_);
v___x_1266_ = lean_uint64_to_usize(v___x_1265_);
v___x_1267_ = lean_usize_of_nat(v___x_1258_);
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = lean_usize_sub(v___x_1267_, v___x_1268_);
v___x_1270_ = lean_usize_land(v___x_1266_, v___x_1269_);
v_bkt_1271_ = lean_array_uget_borrowed(v_buckets_1254_, v___x_1270_);
v___x_1272_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1251_, v_bkt_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v_size_x27_1274_; lean_object* v___x_1275_; lean_object* v_buckets_x27_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1273_ = lean_unsigned_to_nat(1u);
v_size_x27_1274_ = lean_nat_add(v_size_1253_, v___x_1273_);
lean_dec(v_size_1253_);
lean_inc(v_bkt_1271_);
v___x_1275_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1275_, 0, v_a_1251_);
lean_ctor_set(v___x_1275_, 1, v_b_1252_);
lean_ctor_set(v___x_1275_, 2, v_bkt_1271_);
v_buckets_x27_1276_ = lean_array_uset(v_buckets_1254_, v___x_1270_, v___x_1275_);
v___x_1277_ = lean_unsigned_to_nat(4u);
v___x_1278_ = lean_nat_mul(v_size_x27_1274_, v___x_1277_);
v___x_1279_ = lean_unsigned_to_nat(3u);
v___x_1280_ = lean_nat_div(v___x_1278_, v___x_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_array_get_size(v_buckets_x27_1276_);
v___x_1282_ = lean_nat_dec_le(v___x_1280_, v___x_1281_);
lean_dec(v___x_1280_);
if (v___x_1282_ == 0)
{
lean_object* v_val_1283_; lean_object* v___x_1285_; 
v_val_1283_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_buckets_x27_1276_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_val_1283_);
lean_ctor_set(v___x_1256_, 0, v_size_x27_1274_);
v___x_1285_ = v___x_1256_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_size_x27_1274_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_val_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
else
{
lean_object* v___x_1288_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_buckets_x27_1276_);
lean_ctor_set(v___x_1256_, 0, v_size_x27_1274_);
v___x_1288_ = v___x_1256_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_size_x27_1274_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_buckets_x27_1276_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
else
{
lean_object* v___x_1290_; lean_object* v_buckets_x27_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
lean_inc(v_bkt_1271_);
v___x_1290_ = lean_box(0);
v_buckets_x27_1291_ = lean_array_uset(v_buckets_1254_, v___x_1270_, v___x_1290_);
v___x_1292_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1251_, v_b_1252_, v_bkt_1271_);
v___x_1293_ = lean_array_uset(v_buckets_x27_1291_, v___x_1270_, v___x_1292_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1293_);
v___x_1295_ = v___x_1256_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_size_1253_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* v_e_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
switch(lean_obj_tag(v_e_1298_))
{
case 11:
{
lean_object* v_typeName_1306_; lean_object* v_idx_1307_; lean_object* v_struct_1308_; lean_object* v___x_1309_; 
v_typeName_1306_ = lean_ctor_get(v_e_1298_, 0);
v_idx_1307_ = lean_ctor_get(v_e_1298_, 1);
v_struct_1308_ = lean_ctor_get(v_e_1298_, 2);
lean_inc_ref(v_struct_1308_);
v___x_1309_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_struct_1308_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1324_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1324_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1324_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
size_t v___x_1314_; size_t v___x_1315_; uint8_t v___x_1316_; 
v___x_1314_ = lean_ptr_addr(v_struct_1308_);
v___x_1315_ = lean_ptr_addr(v_a_1310_);
v___x_1316_ = lean_usize_dec_eq(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
lean_inc(v_idx_1307_);
lean_inc(v_typeName_1306_);
lean_dec_ref_known(v_e_1298_, 3);
v___x_1317_ = l_Lean_Expr_proj___override(v_typeName_1306_, v_idx_1307_, v_a_1310_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1317_);
v___x_1319_ = v___x_1312_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
else
{
lean_object* v___x_1322_; 
lean_dec(v_a_1310_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v_e_1298_);
v___x_1322_ = v___x_1312_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_e_1298_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1298_, 3);
return v___x_1309_;
}
}
case 7:
{
lean_object* v_binderName_1325_; lean_object* v_binderType_1326_; lean_object* v_body_1327_; uint8_t v_binderInfo_1328_; lean_object* v___x_1329_; 
v_binderName_1325_ = lean_ctor_get(v_e_1298_, 0);
v_binderType_1326_ = lean_ctor_get(v_e_1298_, 1);
v_body_1327_ = lean_ctor_get(v_e_1298_, 2);
v_binderInfo_1328_ = lean_ctor_get_uint8(v_e_1298_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1326_);
v___x_1329_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1326_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1331_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
lean_inc_ref(v_body_1327_);
v___x_1331_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1327_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1358_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1358_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1358_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
size_t v___x_1336_; size_t v___x_1337_; uint8_t v___x_1338_; 
v___x_1336_ = lean_ptr_addr(v_binderType_1326_);
v___x_1337_ = lean_ptr_addr(v_a_1330_);
v___x_1338_ = lean_usize_dec_eq(v___x_1336_, v___x_1337_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
lean_inc(v_binderName_1325_);
lean_dec_ref_known(v_e_1298_, 3);
v___x_1339_ = l_Lean_Expr_forallE___override(v_binderName_1325_, v_a_1330_, v_a_1332_, v_binderInfo_1328_);
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
size_t v___x_1343_; size_t v___x_1344_; uint8_t v___x_1345_; 
v___x_1343_ = lean_ptr_addr(v_body_1327_);
v___x_1344_ = lean_ptr_addr(v_a_1332_);
v___x_1345_ = lean_usize_dec_eq(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
lean_inc(v_binderName_1325_);
lean_dec_ref_known(v_e_1298_, 3);
v___x_1346_ = l_Lean_Expr_forallE___override(v_binderName_1325_, v_a_1330_, v_a_1332_, v_binderInfo_1328_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1346_);
v___x_1348_ = v___x_1334_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
else
{
uint8_t v___x_1350_; 
v___x_1350_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1328_, v_binderInfo_1328_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_inc(v_binderName_1325_);
lean_dec_ref_known(v_e_1298_, 3);
v___x_1351_ = l_Lean_Expr_forallE___override(v_binderName_1325_, v_a_1330_, v_a_1332_, v_binderInfo_1328_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1351_);
v___x_1353_ = v___x_1334_;
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
lean_object* v___x_1356_; 
lean_dec(v_a_1332_);
lean_dec(v_a_1330_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v_e_1298_);
v___x_1356_ = v___x_1334_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_e_1298_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1330_);
lean_dec_ref_known(v_e_1298_, 3);
return v___x_1331_;
}
}
else
{
lean_dec_ref_known(v_e_1298_, 3);
return v___x_1329_;
}
}
case 6:
{
lean_object* v_binderName_1359_; lean_object* v_binderType_1360_; lean_object* v_body_1361_; uint8_t v_binderInfo_1362_; lean_object* v___x_1363_; 
v_binderName_1359_ = lean_ctor_get(v_e_1298_, 0);
v_binderType_1360_ = lean_ctor_get(v_e_1298_, 1);
v_body_1361_ = lean_ctor_get(v_e_1298_, 2);
v_binderInfo_1362_ = lean_ctor_get_uint8(v_e_1298_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1360_);
v___x_1363_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1360_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
lean_inc_ref(v_body_1361_);
v___x_1365_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1361_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1392_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1392_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1392_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
size_t v___x_1370_; size_t v___x_1371_; uint8_t v___x_1372_; 
v___x_1370_ = lean_ptr_addr(v_binderType_1360_);
v___x_1371_ = lean_ptr_addr(v_a_1364_);
v___x_1372_ = lean_usize_dec_eq(v___x_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_inc(v_binderName_1359_);
lean_dec_ref_known(v_e_1298_, 3);
v___x_1373_ = l_Lean_Expr_lam___override(v_binderName_1359_, v_a_1364_, v_a_1366_, v_binderInfo_1362_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1373_);
v___x_1375_ = v___x_1368_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
else
{
size_t v___x_1377_; size_t v___x_1378_; uint8_t v___x_1379_; 
v___x_1377_ = lean_ptr_addr(v_body_1361_);
v___x_1378_ = lean_ptr_addr(v_a_1366_);
v___x_1379_ = lean_usize_dec_eq(v___x_1377_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1382_; 
lean_inc(v_binderName_1359_);
lean_dec_ref_known(v_e_1298_, 3);
v___x_1380_ = l_Lean_Expr_lam___override(v_binderName_1359_, v_a_1364_, v_a_1366_, v_binderInfo_1362_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1380_);
v___x_1382_ = v___x_1368_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
else
{
uint8_t v___x_1384_; 
v___x_1384_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1362_, v_binderInfo_1362_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_inc(v_binderName_1359_);
lean_dec_ref_known(v_e_1298_, 3);
v___x_1385_ = l_Lean_Expr_lam___override(v_binderName_1359_, v_a_1364_, v_a_1366_, v_binderInfo_1362_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1385_);
v___x_1387_ = v___x_1368_;
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
lean_object* v___x_1390_; 
lean_dec(v_a_1366_);
lean_dec(v_a_1364_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v_e_1298_);
v___x_1390_ = v___x_1368_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_e_1298_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1364_);
lean_dec_ref_known(v_e_1298_, 3);
return v___x_1365_;
}
}
else
{
lean_dec_ref_known(v_e_1298_, 3);
return v___x_1363_;
}
}
case 8:
{
lean_object* v_declName_1393_; lean_object* v_type_1394_; lean_object* v_value_1395_; lean_object* v_body_1396_; uint8_t v_nondep_1397_; lean_object* v___x_1398_; 
v_declName_1393_ = lean_ctor_get(v_e_1298_, 0);
v_type_1394_ = lean_ctor_get(v_e_1298_, 1);
v_value_1395_ = lean_ctor_get(v_e_1298_, 2);
v_body_1396_ = lean_ctor_get(v_e_1298_, 3);
v_nondep_1397_ = lean_ctor_get_uint8(v_e_1298_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1394_);
v___x_1398_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_type_1394_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1400_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
lean_inc_ref(v_value_1395_);
v___x_1400_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_value_1395_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1402_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
lean_inc_ref(v_body_1396_);
v___x_1402_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1396_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1431_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1431_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1431_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
size_t v___x_1407_; size_t v___x_1408_; uint8_t v___x_1409_; 
v___x_1407_ = lean_ptr_addr(v_type_1394_);
v___x_1408_ = lean_ptr_addr(v_a_1399_);
v___x_1409_ = lean_usize_dec_eq(v___x_1407_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_inc(v_declName_1393_);
lean_dec_ref_known(v_e_1298_, 4);
v___x_1410_ = l_Lean_Expr_letE___override(v_declName_1393_, v_a_1399_, v_a_1401_, v_a_1403_, v_nondep_1397_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1410_);
v___x_1412_ = v___x_1405_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
else
{
size_t v___x_1414_; size_t v___x_1415_; uint8_t v___x_1416_; 
v___x_1414_ = lean_ptr_addr(v_value_1395_);
v___x_1415_ = lean_ptr_addr(v_a_1401_);
v___x_1416_ = lean_usize_dec_eq(v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
lean_inc(v_declName_1393_);
lean_dec_ref_known(v_e_1298_, 4);
v___x_1417_ = l_Lean_Expr_letE___override(v_declName_1393_, v_a_1399_, v_a_1401_, v_a_1403_, v_nondep_1397_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1417_);
v___x_1419_ = v___x_1405_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
else
{
size_t v___x_1421_; size_t v___x_1422_; uint8_t v___x_1423_; 
v___x_1421_ = lean_ptr_addr(v_body_1396_);
v___x_1422_ = lean_ptr_addr(v_a_1403_);
v___x_1423_ = lean_usize_dec_eq(v___x_1421_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
lean_inc(v_declName_1393_);
lean_dec_ref_known(v_e_1298_, 4);
v___x_1424_ = l_Lean_Expr_letE___override(v_declName_1393_, v_a_1399_, v_a_1401_, v_a_1403_, v_nondep_1397_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1424_);
v___x_1426_ = v___x_1405_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
else
{
lean_object* v___x_1429_; 
lean_dec(v_a_1403_);
lean_dec(v_a_1401_);
lean_dec(v_a_1399_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v_e_1298_);
v___x_1429_ = v___x_1405_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_e_1298_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1401_);
lean_dec(v_a_1399_);
lean_dec_ref_known(v_e_1298_, 4);
return v___x_1402_;
}
}
else
{
lean_dec(v_a_1399_);
lean_dec_ref_known(v_e_1298_, 4);
return v___x_1400_;
}
}
else
{
lean_dec_ref_known(v_e_1298_, 4);
return v___x_1398_;
}
}
case 5:
{
lean_object* v_fn_1432_; lean_object* v_arg_1433_; lean_object* v___x_1434_; 
v_fn_1432_ = lean_ctor_get(v_e_1298_, 0);
v_arg_1433_ = lean_ctor_get(v_e_1298_, 1);
lean_inc_ref(v_fn_1432_);
v___x_1434_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_fn_1432_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1436_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
lean_inc_ref(v_arg_1433_);
v___x_1436_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_arg_1433_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1458_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1458_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1458_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
size_t v___x_1441_; size_t v___x_1442_; uint8_t v___x_1443_; 
v___x_1441_ = lean_ptr_addr(v_fn_1432_);
v___x_1442_ = lean_ptr_addr(v_a_1435_);
v___x_1443_ = lean_usize_dec_eq(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_dec_ref_known(v_e_1298_, 2);
v___x_1444_ = l_Lean_Expr_app___override(v_a_1435_, v_a_1437_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1444_);
v___x_1446_ = v___x_1439_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
else
{
size_t v___x_1448_; size_t v___x_1449_; uint8_t v___x_1450_; 
v___x_1448_ = lean_ptr_addr(v_arg_1433_);
v___x_1449_ = lean_ptr_addr(v_a_1437_);
v___x_1450_ = lean_usize_dec_eq(v___x_1448_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
lean_dec_ref_known(v_e_1298_, 2);
v___x_1451_ = l_Lean_Expr_app___override(v_a_1435_, v_a_1437_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1451_);
v___x_1453_ = v___x_1439_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
else
{
lean_object* v___x_1456_; 
lean_dec(v_a_1437_);
lean_dec(v_a_1435_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v_e_1298_);
v___x_1456_ = v___x_1439_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_e_1298_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
else
{
lean_dec(v_a_1435_);
lean_dec_ref_known(v_e_1298_, 2);
return v___x_1436_;
}
}
else
{
lean_dec_ref_known(v_e_1298_, 2);
return v___x_1434_;
}
}
case 10:
{
lean_object* v_data_1459_; lean_object* v_expr_1460_; lean_object* v___x_1461_; 
v_data_1459_ = lean_ctor_get(v_e_1298_, 0);
v_expr_1460_ = lean_ctor_get(v_e_1298_, 1);
lean_inc_ref(v_expr_1460_);
v___x_1461_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_expr_1460_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1476_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1476_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1476_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
size_t v___x_1466_; size_t v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = lean_ptr_addr(v_expr_1460_);
v___x_1467_ = lean_ptr_addr(v_a_1462_);
v___x_1468_ = lean_usize_dec_eq(v___x_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
lean_inc(v_data_1459_);
lean_dec_ref_known(v_e_1298_, 2);
v___x_1469_ = l_Lean_Expr_mdata___override(v_data_1459_, v_a_1462_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1469_);
v___x_1471_ = v___x_1464_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
else
{
lean_object* v___x_1474_; 
lean_dec(v_a_1462_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v_e_1298_);
v___x_1474_ = v___x_1464_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_e_1298_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1298_, 2);
return v___x_1461_;
}
}
case 3:
{
lean_object* v_u_1477_; lean_object* v___x_1478_; 
v_u_1477_ = lean_ctor_get(v_e_1298_, 0);
lean_inc(v_u_1477_);
v___x_1478_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_1477_, v_a_1300_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1493_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1493_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1493_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
size_t v___x_1483_; size_t v___x_1484_; uint8_t v___x_1485_; 
v___x_1483_ = lean_ptr_addr(v_u_1477_);
v___x_1484_ = lean_ptr_addr(v_a_1479_);
v___x_1485_ = lean_usize_dec_eq(v___x_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
lean_dec_ref_known(v_e_1298_, 1);
v___x_1486_ = l_Lean_Expr_sort___override(v_a_1479_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1486_);
v___x_1488_ = v___x_1481_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
else
{
lean_object* v___x_1491_; 
lean_dec(v_a_1479_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v_e_1298_);
v___x_1491_ = v___x_1481_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_e_1298_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref_known(v_e_1298_, 1);
v_a_1494_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1478_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1478_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
case 4:
{
lean_object* v_declName_1502_; lean_object* v_us_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_declName_1502_ = lean_ctor_get(v_e_1298_, 0);
v_us_1503_ = lean_ctor_get(v_e_1298_, 1);
v___x_1504_ = lean_box(0);
lean_inc(v_us_1503_);
v___x_1505_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_us_1503_, v___x_1504_, v_a_1300_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1518_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1518_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1518_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
uint8_t v___x_1510_; 
v___x_1510_ = l_ptrEqList___redArg(v_us_1503_, v_a_1506_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
lean_inc(v_declName_1502_);
lean_dec_ref_known(v_e_1298_, 2);
v___x_1511_ = l_Lean_Expr_const___override(v_declName_1502_, v_a_1506_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1511_);
v___x_1513_ = v___x_1508_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
else
{
lean_object* v___x_1516_; 
lean_dec(v_a_1506_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v_e_1298_);
v___x_1516_ = v___x_1508_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_e_1298_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref_known(v_e_1298_, 2);
v_a_1519_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1505_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1505_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_1527_; lean_object* v___f_1528_; lean_object* v___x_1529_; 
v_mvarId_1527_ = lean_ctor_get(v_e_1298_, 0);
lean_inc_ref(v_e_1298_);
v___f_1528_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1528_, 0, v_e_1298_);
lean_inc(v_mvarId_1527_);
v___x_1529_ = l_Lean_MVarId_getDecl(v_mvarId_1527_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v_type_1531_; lean_object* v___x_1532_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v_type_1531_ = lean_ctor_get(v_a_1530_, 2);
lean_inc_ref_n(v_type_1531_, 2);
lean_dec(v_a_1530_);
v___x_1532_ = l_Lean_Meta_Closure_preprocess(v_type_1531_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1533_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1536_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v___x_1536_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1538_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1538_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_1300_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1600_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1600_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1600_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v_e_x27_1544_; lean_object* v___y_1545_; lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_1527_, v_a_1302_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
if (lean_obj_tag(v_a_1578_) == 1)
{
lean_object* v_val_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref_known(v_e_1298_, 1);
v_val_1579_ = lean_ctor_get(v_a_1578_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_a_1578_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1581_ = v_a_1578_;
v_isShared_1582_ = v_isSharedCheck_1591_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_val_1579_);
lean_dec(v_a_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1591_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v_fvars_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
v_fvars_1583_ = lean_ctor_get(v_val_1579_, 0);
lean_inc_ref(v_fvars_1583_);
lean_dec(v_val_1579_);
v___x_1584_ = lean_array_get_size(v_fvars_1583_);
lean_dec_ref(v_fvars_1583_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1584_);
v___x_1586_ = v___x_1581_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
uint8_t v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = 0;
v___x_1588_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1531_, v___x_1586_, v___f_1528_, v___x_1587_, v___x_1587_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1588_, 1);
v_e_x27_1544_ = v_a_1589_;
v___y_1545_ = v_a_1300_;
goto v___jp_1543_;
}
else
{
lean_del_object(v___x_1541_);
lean_dec(v_a_1539_);
lean_dec(v_a_1537_);
lean_dec(v_a_1535_);
return v___x_1588_;
}
}
}
}
else
{
lean_dec(v_a_1578_);
lean_dec_ref(v_type_1531_);
lean_dec_ref(v___f_1528_);
v_e_x27_1544_ = v_e_1298_;
v___y_1545_ = v_a_1300_;
goto v___jp_1543_;
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_del_object(v___x_1541_);
lean_dec(v_a_1539_);
lean_dec(v_a_1537_);
lean_dec(v_a_1535_);
lean_dec_ref(v_type_1531_);
lean_dec_ref(v___f_1528_);
lean_dec_ref_known(v_e_1298_, 1);
v_a_1592_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1577_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1577_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
v___jp_1543_:
{
lean_object* v___x_1546_; lean_object* v_visitedLevel_1547_; lean_object* v_visitedExpr_1548_; lean_object* v_levelParams_1549_; lean_object* v_nextLevelIdx_1550_; lean_object* v_levelArgs_1551_; lean_object* v_newLocalDecls_1552_; lean_object* v_newLocalDeclsForMVars_1553_; lean_object* v_newLetDecls_1554_; lean_object* v_nextExprIdx_1555_; lean_object* v_exprMVarArgs_1556_; lean_object* v_exprFVarArgs_1557_; lean_object* v_toProcess_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1576_; 
v___x_1546_ = lean_st_ref_take(v___y_1545_);
v_visitedLevel_1547_ = lean_ctor_get(v___x_1546_, 0);
v_visitedExpr_1548_ = lean_ctor_get(v___x_1546_, 1);
v_levelParams_1549_ = lean_ctor_get(v___x_1546_, 2);
v_nextLevelIdx_1550_ = lean_ctor_get(v___x_1546_, 3);
v_levelArgs_1551_ = lean_ctor_get(v___x_1546_, 4);
v_newLocalDecls_1552_ = lean_ctor_get(v___x_1546_, 5);
v_newLocalDeclsForMVars_1553_ = lean_ctor_get(v___x_1546_, 6);
v_newLetDecls_1554_ = lean_ctor_get(v___x_1546_, 7);
v_nextExprIdx_1555_ = lean_ctor_get(v___x_1546_, 8);
v_exprMVarArgs_1556_ = lean_ctor_get(v___x_1546_, 9);
v_exprFVarArgs_1557_ = lean_ctor_get(v___x_1546_, 10);
v_toProcess_1558_ = lean_ctor_get(v___x_1546_, 11);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1560_ = v___x_1546_;
v_isShared_1561_ = v_isSharedCheck_1576_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_toProcess_1558_);
lean_inc(v_exprFVarArgs_1557_);
lean_inc(v_exprMVarArgs_1556_);
lean_inc(v_nextExprIdx_1555_);
lean_inc(v_newLetDecls_1554_);
lean_inc(v_newLocalDeclsForMVars_1553_);
lean_inc(v_newLocalDecls_1552_);
lean_inc(v_levelArgs_1551_);
lean_inc(v_nextLevelIdx_1550_);
lean_inc(v_levelParams_1549_);
lean_inc(v_visitedExpr_1548_);
lean_inc(v_visitedLevel_1547_);
lean_dec(v___x_1546_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1576_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; uint8_t v___x_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1562_ = lean_unsigned_to_nat(0u);
v___x_1563_ = 0;
v___x_1564_ = 0;
lean_inc(v_a_1537_);
v___x_1565_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1565_, 0, v___x_1562_);
lean_ctor_set(v___x_1565_, 1, v_a_1537_);
lean_ctor_set(v___x_1565_, 2, v_a_1539_);
lean_ctor_set(v___x_1565_, 3, v_a_1535_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*4, v___x_1563_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*4 + 1, v___x_1564_);
v___x_1566_ = lean_array_push(v_newLocalDeclsForMVars_1553_, v___x_1565_);
v___x_1567_ = lean_array_push(v_exprMVarArgs_1556_, v_e_x27_1544_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 9, v___x_1567_);
lean_ctor_set(v___x_1560_, 6, v___x_1566_);
v___x_1569_ = v___x_1560_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_visitedLevel_1547_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_visitedExpr_1548_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_levelParams_1549_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_nextLevelIdx_1550_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_levelArgs_1551_);
lean_ctor_set(v_reuseFailAlloc_1575_, 5, v_newLocalDecls_1552_);
lean_ctor_set(v_reuseFailAlloc_1575_, 6, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1575_, 7, v_newLetDecls_1554_);
lean_ctor_set(v_reuseFailAlloc_1575_, 8, v_nextExprIdx_1555_);
lean_ctor_set(v_reuseFailAlloc_1575_, 9, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1575_, 10, v_exprFVarArgs_1557_);
lean_ctor_set(v_reuseFailAlloc_1575_, 11, v_toProcess_1558_);
v___x_1569_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1570_ = lean_st_ref_put(v___y_1545_, v___x_1569_);
v___x_1571_ = l_Lean_mkFVar(v_a_1537_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1571_);
v___x_1573_ = v___x_1541_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v_a_1537_);
lean_dec(v_a_1535_);
lean_dec_ref(v_type_1531_);
lean_dec_ref(v___f_1528_);
lean_dec_ref_known(v_e_1298_, 1);
v_a_1601_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1538_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1538_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec(v_a_1535_);
lean_dec_ref(v_type_1531_);
lean_dec_ref(v___f_1528_);
lean_dec_ref_known(v_e_1298_, 1);
v_a_1609_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1536_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1536_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_dec_ref(v_type_1531_);
lean_dec_ref(v___f_1528_);
lean_dec_ref_known(v_e_1298_, 1);
return v___x_1534_;
}
}
else
{
lean_dec_ref(v_type_1531_);
lean_dec_ref(v___f_1528_);
lean_dec_ref_known(v_e_1298_, 1);
return v___x_1532_;
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v___f_1528_);
lean_dec_ref_known(v_e_1298_, 1);
v_a_1617_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1529_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1529_);
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
case 1:
{
lean_object* v_fvarId_1625_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; uint8_t v___x_1662_; lean_object* v___x_1663_; 
v_fvarId_1625_ = lean_ctor_get(v_e_1298_, 0);
lean_inc_n(v_fvarId_1625_, 2);
lean_dec_ref_known(v_e_1298_, 1);
v___x_1662_ = 0;
v___x_1663_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_1625_, v___x_1662_, v_a_1301_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1663_) == 0)
{
uint8_t v_zetaDelta_1664_; 
v_zetaDelta_1664_ = lean_ctor_get_uint8(v_a_1299_, 0);
if (v_zetaDelta_1664_ == 1)
{
lean_object* v_a_1665_; 
v_a_1665_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1663_, 1);
if (lean_obj_tag(v_a_1665_) == 1)
{
lean_object* v_val_1666_; lean_object* v___x_1667_; 
lean_dec(v_fvarId_1625_);
v_val_1666_ = lean_ctor_get(v_a_1665_, 0);
lean_inc(v_val_1666_);
lean_dec_ref_known(v_a_1665_, 1);
v___x_1667_ = l_Lean_Meta_Closure_preprocess(v_val_1666_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1668_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
return v___x_1669_;
}
else
{
return v___x_1667_;
}
}
else
{
lean_dec(v_a_1665_);
v___y_1627_ = v_a_1299_;
v___y_1628_ = v_a_1300_;
v___y_1629_ = v_a_1301_;
v___y_1630_ = v_a_1302_;
v___y_1631_ = v_a_1303_;
v___y_1632_ = v_a_1304_;
goto v___jp_1626_;
}
}
else
{
lean_dec_ref_known(v___x_1663_, 1);
v___y_1627_ = v_a_1299_;
v___y_1628_ = v_a_1300_;
v___y_1629_ = v_a_1301_;
v___y_1630_ = v_a_1302_;
v___y_1631_ = v_a_1303_;
v___y_1632_ = v_a_1304_;
goto v___jp_1626_;
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_fvarId_1625_);
v_a_1670_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1663_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1663_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
v___jp_1626_:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc_n(v_a_1634_, 2);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v_fvarId_1625_);
lean_ctor_set(v___x_1635_, 1, v_a_1634_);
v___x_1636_ = l_Lean_Meta_Closure_pushToProcess___redArg(v___x_1635_, v___y_1628_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1644_; 
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; 
v_unused_1645_ = lean_ctor_get(v___x_1636_, 0);
lean_dec(v_unused_1645_);
v___x_1638_ = v___x_1636_;
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
else
{
lean_dec(v___x_1636_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = l_Lean_mkFVar(v_a_1634_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1640_);
v___x_1642_ = v___x_1638_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v_a_1634_);
v_a_1646_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1636_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1636_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v_fvarId_1625_);
v_a_1654_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1633_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1633_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
default: 
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v_e_1298_);
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object* v_e_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
uint8_t v___x_1730_; 
v___x_1730_ = l_Lean_Expr_hasLevelParam(v_e_1679_);
if (v___x_1730_ == 0)
{
uint8_t v___x_1731_; 
v___x_1731_ = l_Lean_Expr_hasFVar(v_e_1679_);
if (v___x_1731_ == 0)
{
uint8_t v___x_1732_; 
v___x_1732_ = l_Lean_Expr_hasMVar(v_e_1679_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_e_1679_);
return v___x_1733_;
}
else
{
goto v___jp_1687_;
}
}
else
{
goto v___jp_1687_;
}
}
else
{
goto v___jp_1687_;
}
v___jp_1687_:
{
lean_object* v___x_1688_; lean_object* v_visitedExpr_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_st_ref_get(v___y_1681_);
v_visitedExpr_1689_ = lean_ctor_get(v___x_1688_, 1);
lean_inc_ref(v_visitedExpr_1689_);
lean_dec(v___x_1688_);
v___x_1690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1689_, v_e_1679_);
lean_dec_ref(v_visitedExpr_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; 
lean_inc_ref(v_e_1679_);
v___x_1691_ = l_Lean_Meta_Closure_collectExprAux(v_e_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1721_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1721_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1721_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v_visitedLevel_1697_; lean_object* v_visitedExpr_1698_; lean_object* v_levelParams_1699_; lean_object* v_nextLevelIdx_1700_; lean_object* v_levelArgs_1701_; lean_object* v_newLocalDecls_1702_; lean_object* v_newLocalDeclsForMVars_1703_; lean_object* v_newLetDecls_1704_; lean_object* v_nextExprIdx_1705_; lean_object* v_exprMVarArgs_1706_; lean_object* v_exprFVarArgs_1707_; lean_object* v_toProcess_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1720_; 
v___x_1696_ = lean_st_ref_take(v___y_1681_);
v_visitedLevel_1697_ = lean_ctor_get(v___x_1696_, 0);
v_visitedExpr_1698_ = lean_ctor_get(v___x_1696_, 1);
v_levelParams_1699_ = lean_ctor_get(v___x_1696_, 2);
v_nextLevelIdx_1700_ = lean_ctor_get(v___x_1696_, 3);
v_levelArgs_1701_ = lean_ctor_get(v___x_1696_, 4);
v_newLocalDecls_1702_ = lean_ctor_get(v___x_1696_, 5);
v_newLocalDeclsForMVars_1703_ = lean_ctor_get(v___x_1696_, 6);
v_newLetDecls_1704_ = lean_ctor_get(v___x_1696_, 7);
v_nextExprIdx_1705_ = lean_ctor_get(v___x_1696_, 8);
v_exprMVarArgs_1706_ = lean_ctor_get(v___x_1696_, 9);
v_exprFVarArgs_1707_ = lean_ctor_get(v___x_1696_, 10);
v_toProcess_1708_ = lean_ctor_get(v___x_1696_, 11);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1710_ = v___x_1696_;
v_isShared_1711_ = v_isSharedCheck_1720_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_toProcess_1708_);
lean_inc(v_exprFVarArgs_1707_);
lean_inc(v_exprMVarArgs_1706_);
lean_inc(v_nextExprIdx_1705_);
lean_inc(v_newLetDecls_1704_);
lean_inc(v_newLocalDeclsForMVars_1703_);
lean_inc(v_newLocalDecls_1702_);
lean_inc(v_levelArgs_1701_);
lean_inc(v_nextLevelIdx_1700_);
lean_inc(v_levelParams_1699_);
lean_inc(v_visitedExpr_1698_);
lean_inc(v_visitedLevel_1697_);
lean_dec(v___x_1696_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1720_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
lean_inc(v_a_1692_);
v___x_1712_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1698_, v_e_1679_, v_a_1692_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 1, v___x_1712_);
v___x_1714_ = v___x_1710_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_visitedLevel_1697_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1719_, 2, v_levelParams_1699_);
lean_ctor_set(v_reuseFailAlloc_1719_, 3, v_nextLevelIdx_1700_);
lean_ctor_set(v_reuseFailAlloc_1719_, 4, v_levelArgs_1701_);
lean_ctor_set(v_reuseFailAlloc_1719_, 5, v_newLocalDecls_1702_);
lean_ctor_set(v_reuseFailAlloc_1719_, 6, v_newLocalDeclsForMVars_1703_);
lean_ctor_set(v_reuseFailAlloc_1719_, 7, v_newLetDecls_1704_);
lean_ctor_set(v_reuseFailAlloc_1719_, 8, v_nextExprIdx_1705_);
lean_ctor_set(v_reuseFailAlloc_1719_, 9, v_exprMVarArgs_1706_);
lean_ctor_set(v_reuseFailAlloc_1719_, 10, v_exprFVarArgs_1707_);
lean_ctor_set(v_reuseFailAlloc_1719_, 11, v_toProcess_1708_);
v___x_1714_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = lean_st_ref_put(v___y_1681_, v___x_1714_);
if (v_isShared_1695_ == 0)
{
v___x_1717_ = v___x_1694_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1692_);
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
}
else
{
lean_dec_ref(v_e_1679_);
return v___x_1691_;
}
}
else
{
lean_object* v_val_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec_ref(v_e_1679_);
v_val_1722_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1690_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_val_1722_);
lean_dec(v___x_1690_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 0);
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_val_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object* v_e_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_e_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* v_e_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Meta_Closure_collectExprAux(v_e_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object* v_00_u03b2_1752_, lean_object* v_m_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1753_, v_a_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object* v_00_u03b2_1756_, lean_object* v_m_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(v_00_u03b2_1756_, v_m_1757_, v_a_1758_);
lean_dec_ref(v_a_1758_);
lean_dec_ref(v_m_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object* v_00_u03b2_1760_, lean_object* v_m_1761_, lean_object* v_a_1762_, lean_object* v_b_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_1761_, v_a_1762_, v_b_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object* v_x_1765_, lean_object* v_x_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1765_, v_x_1766_, v___y_1768_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object* v_x_1775_, lean_object* v_x_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(v_x_1775_, v_x_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___boxed(lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object* v_00_u03b2_1801_, lean_object* v_a_1802_, lean_object* v_x_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1802_, v_x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1805_, lean_object* v_a_1806_, lean_object* v_x_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(v_00_u03b2_1805_, v_a_1806_, v_x_1807_);
lean_dec(v_x_1807_);
lean_dec_ref(v_a_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object* v_00_u03b2_1809_, lean_object* v_a_1810_, lean_object* v_x_1811_){
_start:
{
uint8_t v___x_1812_; 
v___x_1812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1810_, v_x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1813_, lean_object* v_a_1814_, lean_object* v_x_1815_){
_start:
{
uint8_t v_res_1816_; lean_object* v_r_1817_; 
v_res_1816_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(v_00_u03b2_1813_, v_a_1814_, v_x_1815_);
lean_dec(v_x_1815_);
lean_dec_ref(v_a_1814_);
v_r_1817_ = lean_box(v_res_1816_);
return v_r_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3(lean_object* v_00_u03b2_1818_, lean_object* v_data_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_data_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4(lean_object* v_00_u03b2_1821_, lean_object* v_a_1822_, lean_object* v_b_1823_, lean_object* v_x_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1822_, v_b_1823_, v_x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1826_, lean_object* v_i_1827_, lean_object* v_source_1828_, lean_object* v_target_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v_i_1827_, v_source_1828_, v_target_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_x_1832_, v_x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* v_e_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_Meta_Closure_preprocess(v_e_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; uint8_t v___x_1888_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v___x_1888_ = l_Lean_Expr_hasLevelParam(v_a_1844_);
if (v___x_1888_ == 0)
{
uint8_t v___x_1889_; 
v___x_1889_ = l_Lean_Expr_hasFVar(v_a_1844_);
if (v___x_1889_ == 0)
{
uint8_t v___x_1890_; 
v___x_1890_ = l_Lean_Expr_hasMVar(v_a_1844_);
if (v___x_1890_ == 0)
{
return v___x_1843_;
}
else
{
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
goto v___jp_1845_;
}
}
else
{
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
goto v___jp_1845_;
}
}
else
{
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
goto v___jp_1845_;
}
v___jp_1845_:
{
lean_object* v___x_1846_; lean_object* v_visitedExpr_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_st_ref_get(v_a_1837_);
v_visitedExpr_1847_ = lean_ctor_get(v___x_1846_, 1);
lean_inc_ref(v_visitedExpr_1847_);
lean_dec(v___x_1846_);
v___x_1848_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1847_, v_a_1844_);
lean_dec_ref(v_visitedExpr_1847_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v___x_1849_; 
lean_inc(v_a_1844_);
v___x_1849_ = l_Lean_Meta_Closure_collectExprAux(v_a_1844_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1879_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1879_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1879_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v_visitedLevel_1855_; lean_object* v_visitedExpr_1856_; lean_object* v_levelParams_1857_; lean_object* v_nextLevelIdx_1858_; lean_object* v_levelArgs_1859_; lean_object* v_newLocalDecls_1860_; lean_object* v_newLocalDeclsForMVars_1861_; lean_object* v_newLetDecls_1862_; lean_object* v_nextExprIdx_1863_; lean_object* v_exprMVarArgs_1864_; lean_object* v_exprFVarArgs_1865_; lean_object* v_toProcess_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1878_; 
v___x_1854_ = lean_st_ref_take(v_a_1837_);
v_visitedLevel_1855_ = lean_ctor_get(v___x_1854_, 0);
v_visitedExpr_1856_ = lean_ctor_get(v___x_1854_, 1);
v_levelParams_1857_ = lean_ctor_get(v___x_1854_, 2);
v_nextLevelIdx_1858_ = lean_ctor_get(v___x_1854_, 3);
v_levelArgs_1859_ = lean_ctor_get(v___x_1854_, 4);
v_newLocalDecls_1860_ = lean_ctor_get(v___x_1854_, 5);
v_newLocalDeclsForMVars_1861_ = lean_ctor_get(v___x_1854_, 6);
v_newLetDecls_1862_ = lean_ctor_get(v___x_1854_, 7);
v_nextExprIdx_1863_ = lean_ctor_get(v___x_1854_, 8);
v_exprMVarArgs_1864_ = lean_ctor_get(v___x_1854_, 9);
v_exprFVarArgs_1865_ = lean_ctor_get(v___x_1854_, 10);
v_toProcess_1866_ = lean_ctor_get(v___x_1854_, 11);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1868_ = v___x_1854_;
v_isShared_1869_ = v_isSharedCheck_1878_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_toProcess_1866_);
lean_inc(v_exprFVarArgs_1865_);
lean_inc(v_exprMVarArgs_1864_);
lean_inc(v_nextExprIdx_1863_);
lean_inc(v_newLetDecls_1862_);
lean_inc(v_newLocalDeclsForMVars_1861_);
lean_inc(v_newLocalDecls_1860_);
lean_inc(v_levelArgs_1859_);
lean_inc(v_nextLevelIdx_1858_);
lean_inc(v_levelParams_1857_);
lean_inc(v_visitedExpr_1856_);
lean_inc(v_visitedLevel_1855_);
lean_dec(v___x_1854_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1878_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_inc(v_a_1850_);
v___x_1870_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1856_, v_a_1844_, v_a_1850_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___x_1870_);
v___x_1872_ = v___x_1868_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_visitedLevel_1855_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v___x_1870_);
lean_ctor_set(v_reuseFailAlloc_1877_, 2, v_levelParams_1857_);
lean_ctor_set(v_reuseFailAlloc_1877_, 3, v_nextLevelIdx_1858_);
lean_ctor_set(v_reuseFailAlloc_1877_, 4, v_levelArgs_1859_);
lean_ctor_set(v_reuseFailAlloc_1877_, 5, v_newLocalDecls_1860_);
lean_ctor_set(v_reuseFailAlloc_1877_, 6, v_newLocalDeclsForMVars_1861_);
lean_ctor_set(v_reuseFailAlloc_1877_, 7, v_newLetDecls_1862_);
lean_ctor_set(v_reuseFailAlloc_1877_, 8, v_nextExprIdx_1863_);
lean_ctor_set(v_reuseFailAlloc_1877_, 9, v_exprMVarArgs_1864_);
lean_ctor_set(v_reuseFailAlloc_1877_, 10, v_exprFVarArgs_1865_);
lean_ctor_set(v_reuseFailAlloc_1877_, 11, v_toProcess_1866_);
v___x_1872_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = lean_st_ref_put(v_a_1837_, v___x_1872_);
if (v_isShared_1853_ == 0)
{
v___x_1875_ = v___x_1852_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1850_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
else
{
lean_dec(v_a_1844_);
return v___x_1849_;
}
}
else
{
lean_object* v_val_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_a_1844_);
v_val_1880_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1848_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_val_1880_);
lean_dec(v___x_1848_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set_tag(v___x_1882_, 0);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_val_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
else
{
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* v_e_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_Meta_Closure_collectExpr(v_e_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* v_lctx_1900_, lean_object* v_i_1901_, lean_object* v_toProcess_1902_, lean_object* v_elem_1903_){
_start:
{
lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = lean_array_get_size(v_toProcess_1902_);
v___x_1905_ = lean_nat_dec_lt(v_i_1901_, v___x_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; 
lean_dec(v_i_1901_);
lean_dec_ref(v_lctx_1900_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v_elem_1903_);
lean_ctor_set(v___x_1906_, 1, v_toProcess_1902_);
return v___x_1906_;
}
else
{
lean_object* v_fvarId_1907_; lean_object* v_elem_x27_1908_; lean_object* v_fvarId_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v_fvarId_1907_ = lean_ctor_get(v_elem_1903_, 0);
v_elem_x27_1908_ = lean_array_fget_borrowed(v_toProcess_1902_, v_i_1901_);
v_fvarId_1909_ = lean_ctor_get(v_elem_x27_1908_, 0);
lean_inc(v_fvarId_1907_);
lean_inc_ref_n(v_lctx_1900_, 2);
v___x_1910_ = l_Lean_LocalContext_get_x21(v_lctx_1900_, v_fvarId_1907_);
v___x_1911_ = l_Lean_LocalDecl_index(v___x_1910_);
lean_dec_ref(v___x_1910_);
lean_inc(v_fvarId_1909_);
v___x_1912_ = l_Lean_LocalContext_get_x21(v_lctx_1900_, v_fvarId_1909_);
v___x_1913_ = l_Lean_LocalDecl_index(v___x_1912_);
lean_dec_ref(v___x_1912_);
v___x_1914_ = lean_nat_dec_lt(v___x_1911_, v___x_1913_);
lean_dec(v___x_1913_);
lean_dec(v___x_1911_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_unsigned_to_nat(1u);
v___x_1916_ = lean_nat_add(v_i_1901_, v___x_1915_);
lean_dec(v_i_1901_);
v_i_1901_ = v___x_1916_;
goto _start;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_inc(v_elem_x27_1908_);
v___x_1918_ = lean_unsigned_to_nat(1u);
v___x_1919_ = lean_nat_add(v_i_1901_, v___x_1918_);
v___x_1920_ = lean_array_fset(v_toProcess_1902_, v_i_1901_, v_elem_1903_);
lean_dec(v_i_1901_);
v_i_1901_ = v___x_1919_;
v_toProcess_1902_ = v___x_1920_;
v_elem_1903_ = v_elem_x27_1908_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_lctx_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v_toProcess_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v_lctx_1925_ = lean_ctor_get(v_a_1923_, 2);
v___x_1926_ = ((lean_object*)(l_Lean_Meta_Closure_instInhabitedToProcessElement_default));
v___x_1927_ = lean_st_ref_get(v_a_1922_);
v_toProcess_1928_ = lean_ctor_get(v___x_1927_, 11);
lean_inc_ref(v_toProcess_1928_);
lean_dec(v___x_1927_);
v___x_1929_ = lean_array_get_size(v_toProcess_1928_);
lean_dec_ref(v_toProcess_1928_);
v___x_1930_ = lean_unsigned_to_nat(0u);
v___x_1931_ = lean_nat_dec_eq(v___x_1929_, v___x_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v_visitedLevel_1933_; lean_object* v_visitedExpr_1934_; lean_object* v_levelParams_1935_; lean_object* v_nextLevelIdx_1936_; lean_object* v_levelArgs_1937_; lean_object* v_newLocalDecls_1938_; lean_object* v_newLocalDeclsForMVars_1939_; lean_object* v_newLetDecls_1940_; lean_object* v_nextExprIdx_1941_; lean_object* v_exprMVarArgs_1942_; lean_object* v_exprFVarArgs_1943_; lean_object* v_toProcess_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1962_; 
v___x_1932_ = lean_st_ref_take(v_a_1922_);
v_visitedLevel_1933_ = lean_ctor_get(v___x_1932_, 0);
v_visitedExpr_1934_ = lean_ctor_get(v___x_1932_, 1);
v_levelParams_1935_ = lean_ctor_get(v___x_1932_, 2);
v_nextLevelIdx_1936_ = lean_ctor_get(v___x_1932_, 3);
v_levelArgs_1937_ = lean_ctor_get(v___x_1932_, 4);
v_newLocalDecls_1938_ = lean_ctor_get(v___x_1932_, 5);
v_newLocalDeclsForMVars_1939_ = lean_ctor_get(v___x_1932_, 6);
v_newLetDecls_1940_ = lean_ctor_get(v___x_1932_, 7);
v_nextExprIdx_1941_ = lean_ctor_get(v___x_1932_, 8);
v_exprMVarArgs_1942_ = lean_ctor_get(v___x_1932_, 9);
v_exprFVarArgs_1943_ = lean_ctor_get(v___x_1932_, 10);
v_toProcess_1944_ = lean_ctor_get(v___x_1932_, 11);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1946_ = v___x_1932_;
v_isShared_1947_ = v_isSharedCheck_1962_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_toProcess_1944_);
lean_inc(v_exprFVarArgs_1943_);
lean_inc(v_exprMVarArgs_1942_);
lean_inc(v_nextExprIdx_1941_);
lean_inc(v_newLetDecls_1940_);
lean_inc(v_newLocalDeclsForMVars_1939_);
lean_inc(v_newLocalDecls_1938_);
lean_inc(v_levelArgs_1937_);
lean_inc(v_nextLevelIdx_1936_);
lean_inc(v_levelParams_1935_);
lean_inc(v_visitedExpr_1934_);
lean_inc(v_visitedLevel_1933_);
lean_dec(v___x_1932_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1962_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v_fst_1954_; lean_object* v_snd_1955_; lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1948_ = lean_array_get_size(v_toProcess_1944_);
v___x_1949_ = lean_unsigned_to_nat(1u);
v___x_1950_ = lean_nat_sub(v___x_1948_, v___x_1949_);
v___x_1951_ = lean_array_get(v___x_1926_, v_toProcess_1944_, v___x_1950_);
lean_dec(v___x_1950_);
v___x_1952_ = lean_array_pop(v_toProcess_1944_);
lean_inc_ref(v_lctx_1925_);
v___x_1953_ = l_Lean_Meta_Closure_pickNextToProcessAux(v_lctx_1925_, v___x_1930_, v___x_1952_, v___x_1951_);
v_fst_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_fst_1954_);
v_snd_1955_ = lean_ctor_get(v___x_1953_, 1);
lean_inc(v_snd_1955_);
lean_dec_ref(v___x_1953_);
v___x_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1956_, 0, v_fst_1954_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 11, v_snd_1955_);
v___x_1958_ = v___x_1946_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_visitedLevel_1933_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_visitedExpr_1934_);
lean_ctor_set(v_reuseFailAlloc_1961_, 2, v_levelParams_1935_);
lean_ctor_set(v_reuseFailAlloc_1961_, 3, v_nextLevelIdx_1936_);
lean_ctor_set(v_reuseFailAlloc_1961_, 4, v_levelArgs_1937_);
lean_ctor_set(v_reuseFailAlloc_1961_, 5, v_newLocalDecls_1938_);
lean_ctor_set(v_reuseFailAlloc_1961_, 6, v_newLocalDeclsForMVars_1939_);
lean_ctor_set(v_reuseFailAlloc_1961_, 7, v_newLetDecls_1940_);
lean_ctor_set(v_reuseFailAlloc_1961_, 8, v_nextExprIdx_1941_);
lean_ctor_set(v_reuseFailAlloc_1961_, 9, v_exprMVarArgs_1942_);
lean_ctor_set(v_reuseFailAlloc_1961_, 10, v_exprFVarArgs_1943_);
lean_ctor_set(v_reuseFailAlloc_1961_, 11, v_snd_1955_);
v___x_1958_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_st_ref_put(v_a_1922_, v___x_1958_);
v___x_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1956_);
return v___x_1960_;
}
}
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1965_, v_a_1966_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1970_, v_a_1971_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Meta_Closure_pickNextToProcess_x3f(v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object* v_e_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v___x_1988_; lean_object* v_visitedLevel_1989_; lean_object* v_visitedExpr_1990_; lean_object* v_levelParams_1991_; lean_object* v_nextLevelIdx_1992_; lean_object* v_levelArgs_1993_; lean_object* v_newLocalDecls_1994_; lean_object* v_newLocalDeclsForMVars_1995_; lean_object* v_newLetDecls_1996_; lean_object* v_nextExprIdx_1997_; lean_object* v_exprMVarArgs_1998_; lean_object* v_exprFVarArgs_1999_; lean_object* v_toProcess_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2011_; 
v___x_1988_ = lean_st_ref_take(v_a_1986_);
v_visitedLevel_1989_ = lean_ctor_get(v___x_1988_, 0);
v_visitedExpr_1990_ = lean_ctor_get(v___x_1988_, 1);
v_levelParams_1991_ = lean_ctor_get(v___x_1988_, 2);
v_nextLevelIdx_1992_ = lean_ctor_get(v___x_1988_, 3);
v_levelArgs_1993_ = lean_ctor_get(v___x_1988_, 4);
v_newLocalDecls_1994_ = lean_ctor_get(v___x_1988_, 5);
v_newLocalDeclsForMVars_1995_ = lean_ctor_get(v___x_1988_, 6);
v_newLetDecls_1996_ = lean_ctor_get(v___x_1988_, 7);
v_nextExprIdx_1997_ = lean_ctor_get(v___x_1988_, 8);
v_exprMVarArgs_1998_ = lean_ctor_get(v___x_1988_, 9);
v_exprFVarArgs_1999_ = lean_ctor_get(v___x_1988_, 10);
v_toProcess_2000_ = lean_ctor_get(v___x_1988_, 11);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2002_ = v___x_1988_;
v_isShared_2003_ = v_isSharedCheck_2011_;
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
lean_dec(v___x_1988_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2011_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2004_ = lean_box(0);
v___x_2005_ = lean_array_push(v_exprFVarArgs_1999_, v_e_1985_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 10, v___x_2005_);
v___x_2007_ = v___x_2002_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_visitedLevel_1989_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_visitedExpr_1990_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_levelParams_1991_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v_nextLevelIdx_1992_);
lean_ctor_set(v_reuseFailAlloc_2010_, 4, v_levelArgs_1993_);
lean_ctor_set(v_reuseFailAlloc_2010_, 5, v_newLocalDecls_1994_);
lean_ctor_set(v_reuseFailAlloc_2010_, 6, v_newLocalDeclsForMVars_1995_);
lean_ctor_set(v_reuseFailAlloc_2010_, 7, v_newLetDecls_1996_);
lean_ctor_set(v_reuseFailAlloc_2010_, 8, v_nextExprIdx_1997_);
lean_ctor_set(v_reuseFailAlloc_2010_, 9, v_exprMVarArgs_1998_);
lean_ctor_set(v_reuseFailAlloc_2010_, 10, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2010_, 11, v_toProcess_2000_);
v___x_2007_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_st_ref_put(v_a_1986_, v___x_2007_);
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2004_);
return v___x_2009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object* v_e_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2012_, v_a_2013_);
lean_dec(v_a_2013_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* v_e_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2016_, v_a_2018_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* v_e_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Lean_Meta_Closure_pushFVarArg(v_e_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* v_newFVarId_2034_, lean_object* v_userName_2035_, lean_object* v_type_2036_, uint8_t v_bi_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Meta_Closure_collectExpr(v_type_2036_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2079_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2079_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2079_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v_visitedLevel_2051_; lean_object* v_visitedExpr_2052_; lean_object* v_levelParams_2053_; lean_object* v_nextLevelIdx_2054_; lean_object* v_levelArgs_2055_; lean_object* v_newLocalDecls_2056_; lean_object* v_newLocalDeclsForMVars_2057_; lean_object* v_newLetDecls_2058_; lean_object* v_nextExprIdx_2059_; lean_object* v_exprMVarArgs_2060_; lean_object* v_exprFVarArgs_2061_; lean_object* v_toProcess_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2078_; 
v___x_2050_ = lean_st_ref_take(v_a_2039_);
v_visitedLevel_2051_ = lean_ctor_get(v___x_2050_, 0);
v_visitedExpr_2052_ = lean_ctor_get(v___x_2050_, 1);
v_levelParams_2053_ = lean_ctor_get(v___x_2050_, 2);
v_nextLevelIdx_2054_ = lean_ctor_get(v___x_2050_, 3);
v_levelArgs_2055_ = lean_ctor_get(v___x_2050_, 4);
v_newLocalDecls_2056_ = lean_ctor_get(v___x_2050_, 5);
v_newLocalDeclsForMVars_2057_ = lean_ctor_get(v___x_2050_, 6);
v_newLetDecls_2058_ = lean_ctor_get(v___x_2050_, 7);
v_nextExprIdx_2059_ = lean_ctor_get(v___x_2050_, 8);
v_exprMVarArgs_2060_ = lean_ctor_get(v___x_2050_, 9);
v_exprFVarArgs_2061_ = lean_ctor_get(v___x_2050_, 10);
v_toProcess_2062_ = lean_ctor_get(v___x_2050_, 11);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2064_ = v___x_2050_;
v_isShared_2065_ = v_isSharedCheck_2078_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_toProcess_2062_);
lean_inc(v_exprFVarArgs_2061_);
lean_inc(v_exprMVarArgs_2060_);
lean_inc(v_nextExprIdx_2059_);
lean_inc(v_newLetDecls_2058_);
lean_inc(v_newLocalDeclsForMVars_2057_);
lean_inc(v_newLocalDecls_2056_);
lean_inc(v_levelArgs_2055_);
lean_inc(v_nextLevelIdx_2054_);
lean_inc(v_levelParams_2053_);
lean_inc(v_visitedExpr_2052_);
lean_inc(v_visitedLevel_2051_);
lean_dec(v___x_2050_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2078_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2066_ = lean_box(0);
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = 0;
v___x_2069_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v_newFVarId_2034_);
lean_ctor_set(v___x_2069_, 2, v_userName_2035_);
lean_ctor_set(v___x_2069_, 3, v_a_2046_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*4, v_bi_2037_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*4 + 1, v___x_2068_);
v___x_2070_ = lean_array_push(v_newLocalDecls_2056_, v___x_2069_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 5, v___x_2070_);
v___x_2072_ = v___x_2064_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_visitedLevel_2051_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_visitedExpr_2052_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_levelParams_2053_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_nextLevelIdx_2054_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v_levelArgs_2055_);
lean_ctor_set(v_reuseFailAlloc_2077_, 5, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2077_, 6, v_newLocalDeclsForMVars_2057_);
lean_ctor_set(v_reuseFailAlloc_2077_, 7, v_newLetDecls_2058_);
lean_ctor_set(v_reuseFailAlloc_2077_, 8, v_nextExprIdx_2059_);
lean_ctor_set(v_reuseFailAlloc_2077_, 9, v_exprMVarArgs_2060_);
lean_ctor_set(v_reuseFailAlloc_2077_, 10, v_exprFVarArgs_2061_);
lean_ctor_set(v_reuseFailAlloc_2077_, 11, v_toProcess_2062_);
v___x_2072_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = lean_st_ref_put(v_a_2039_, v___x_2072_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2066_);
v___x_2075_ = v___x_2048_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2066_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v_userName_2035_);
lean_dec(v_newFVarId_2034_);
v_a_2080_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2045_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2045_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* v_newFVarId_2088_, lean_object* v_userName_2089_, lean_object* v_type_2090_, lean_object* v_bi_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_){
_start:
{
uint8_t v_bi_boxed_2099_; lean_object* v_res_2100_; 
v_bi_boxed_2099_ = lean_unbox(v_bi_2091_);
v_res_2100_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2088_, v_userName_2089_, v_type_2090_, v_bi_boxed_2099_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2100_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(lean_object* v_k_2101_, lean_object* v_t_2102_){
_start:
{
if (lean_obj_tag(v_t_2102_) == 0)
{
lean_object* v_k_2103_; lean_object* v_l_2104_; lean_object* v_r_2105_; uint8_t v___x_2106_; 
v_k_2103_ = lean_ctor_get(v_t_2102_, 1);
v_l_2104_ = lean_ctor_get(v_t_2102_, 3);
v_r_2105_ = lean_ctor_get(v_t_2102_, 4);
v___x_2106_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2101_, v_k_2103_);
switch(v___x_2106_)
{
case 0:
{
v_t_2102_ = v_l_2104_;
goto _start;
}
case 1:
{
uint8_t v___x_2108_; 
v___x_2108_ = 1;
return v___x_2108_;
}
default: 
{
v_t_2102_ = v_r_2105_;
goto _start;
}
}
}
else
{
uint8_t v___x_2110_; 
v___x_2110_ = 0;
return v___x_2110_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object* v_k_2111_, lean_object* v_t_2112_){
_start:
{
uint8_t v_res_2113_; lean_object* v_r_2114_; 
v_res_2113_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2111_, v_t_2112_);
lean_dec(v_t_2112_);
lean_dec(v_k_2111_);
v_r_2114_ = lean_box(v_res_2113_);
return v_r_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(lean_object* v_newFVarId_2115_, lean_object* v_a_2116_, size_t v_sz_2117_, size_t v_i_2118_, lean_object* v_bs_2119_){
_start:
{
uint8_t v___x_2120_; 
v___x_2120_ = lean_usize_dec_lt(v_i_2118_, v_sz_2117_);
if (v___x_2120_ == 0)
{
lean_dec(v_newFVarId_2115_);
return v_bs_2119_;
}
else
{
lean_object* v_v_2121_; lean_object* v___x_2122_; lean_object* v_bs_x27_2123_; lean_object* v___x_2124_; size_t v___x_2125_; size_t v___x_2126_; lean_object* v___x_2127_; 
v_v_2121_ = lean_array_uget(v_bs_2119_, v_i_2118_);
v___x_2122_ = lean_unsigned_to_nat(0u);
v_bs_x27_2123_ = lean_array_uset(v_bs_2119_, v_i_2118_, v___x_2122_);
lean_inc(v_newFVarId_2115_);
v___x_2124_ = l_Lean_LocalDecl_replaceFVarId(v_newFVarId_2115_, v_a_2116_, v_v_2121_);
v___x_2125_ = ((size_t)1ULL);
v___x_2126_ = lean_usize_add(v_i_2118_, v___x_2125_);
v___x_2127_ = lean_array_uset(v_bs_x27_2123_, v_i_2118_, v___x_2124_);
v_i_2118_ = v___x_2126_;
v_bs_2119_ = v___x_2127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(lean_object* v_newFVarId_2129_, lean_object* v_a_2130_, lean_object* v_sz_2131_, lean_object* v_i_2132_, lean_object* v_bs_2133_){
_start:
{
size_t v_sz_boxed_2134_; size_t v_i_boxed_2135_; lean_object* v_res_2136_; 
v_sz_boxed_2134_ = lean_unbox_usize(v_sz_2131_);
lean_dec(v_sz_2131_);
v_i_boxed_2135_ = lean_unbox_usize(v_i_2132_);
lean_dec(v_i_2132_);
v_res_2136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2129_, v_a_2130_, v_sz_boxed_2134_, v_i_boxed_2135_, v_bs_2133_);
lean_dec_ref(v_a_2130_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2138_, v_a_2139_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2272_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2147_ = v___x_2144_;
v_isShared_2148_ = v_isSharedCheck_2272_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2272_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
if (lean_obj_tag(v_a_2145_) == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = lean_box(0);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2149_);
v___x_2151_ = v___x_2147_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
else
{
lean_object* v_val_2153_; lean_object* v_fvarId_2154_; lean_object* v_newFVarId_2155_; lean_object* v___x_2156_; 
lean_del_object(v___x_2147_);
v_val_2153_ = lean_ctor_get(v_a_2145_, 0);
lean_inc(v_val_2153_);
lean_dec_ref_known(v_a_2145_, 1);
v_fvarId_2154_ = lean_ctor_get(v_val_2153_, 0);
lean_inc_n(v_fvarId_2154_, 2);
v_newFVarId_2155_ = lean_ctor_get(v_val_2153_, 1);
lean_inc(v_newFVarId_2155_);
lean_dec(v_val_2153_);
v___x_2156_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_2154_, v_a_2139_, v_a_2141_, v_a_2142_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
if (lean_obj_tag(v_a_2157_) == 0)
{
lean_object* v_userName_2158_; lean_object* v_type_2159_; uint8_t v_bi_2160_; lean_object* v___x_2161_; 
v_userName_2158_ = lean_ctor_get(v_a_2157_, 2);
lean_inc(v_userName_2158_);
v_type_2159_ = lean_ctor_get(v_a_2157_, 3);
lean_inc_ref(v_type_2159_);
v_bi_2160_ = lean_ctor_get_uint8(v_a_2157_, sizeof(void*)*4);
lean_dec_ref_known(v_a_2157_, 4);
v___x_2161_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2155_, v_userName_2158_, v_type_2159_, v_bi_2160_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
lean_dec_ref_known(v___x_2161_, 1);
v___x_2162_ = l_Lean_mkFVar(v_fvarId_2154_);
v___x_2163_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2162_, v_a_2138_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_dec_ref_known(v___x_2163_, 1);
goto _start;
}
else
{
return v___x_2163_;
}
}
else
{
lean_dec(v_fvarId_2154_);
return v___x_2161_;
}
}
else
{
lean_object* v_userName_2165_; lean_object* v_type_2166_; lean_object* v_value_2167_; uint8_t v_nondep_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2261_; 
v_userName_2165_ = lean_ctor_get(v_a_2157_, 2);
v_type_2166_ = lean_ctor_get(v_a_2157_, 3);
v_value_2167_ = lean_ctor_get(v_a_2157_, 4);
v_nondep_2168_ = lean_ctor_get_uint8(v_a_2157_, sizeof(void*)*5);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_a_2157_);
if (v_isSharedCheck_2261_ == 0)
{
lean_object* v_unused_2262_; lean_object* v_unused_2263_; 
v_unused_2262_ = lean_ctor_get(v_a_2157_, 1);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_a_2157_, 0);
lean_dec(v_unused_2263_);
v___x_2170_ = v_a_2157_;
v_isShared_2171_ = v_isSharedCheck_2261_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_value_2167_);
lean_inc(v_type_2166_);
lean_inc(v_userName_2165_);
lean_dec(v_a_2157_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2261_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v_a_2140_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
if (v_nondep_2168_ == 0)
{
uint8_t v___x_2180_; 
v___x_2180_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_fvarId_2154_, v_a_2173_);
lean_dec(v_a_2173_);
if (v___x_2180_ == 0)
{
lean_del_object(v___x_2170_);
lean_dec_ref(v_value_2167_);
goto v___jp_2174_;
}
else
{
lean_object* v___x_2181_; 
lean_dec(v_fvarId_2154_);
v___x_2181_ = l_Lean_Meta_Closure_collectExpr(v_type_2166_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2183_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref_known(v___x_2181_, 1);
v___x_2183_ = l_Lean_Meta_Closure_collectExpr(v_value_2167_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2185_; lean_object* v_visitedLevel_2186_; lean_object* v_visitedExpr_2187_; lean_object* v_levelParams_2188_; lean_object* v_nextLevelIdx_2189_; lean_object* v_levelArgs_2190_; lean_object* v_newLocalDecls_2191_; lean_object* v_newLocalDeclsForMVars_2192_; lean_object* v_newLetDecls_2193_; lean_object* v_nextExprIdx_2194_; lean_object* v_exprMVarArgs_2195_; lean_object* v_exprFVarArgs_2196_; lean_object* v_toProcess_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2236_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v___x_2185_ = lean_st_ref_take(v_a_2138_);
v_visitedLevel_2186_ = lean_ctor_get(v___x_2185_, 0);
v_visitedExpr_2187_ = lean_ctor_get(v___x_2185_, 1);
v_levelParams_2188_ = lean_ctor_get(v___x_2185_, 2);
v_nextLevelIdx_2189_ = lean_ctor_get(v___x_2185_, 3);
v_levelArgs_2190_ = lean_ctor_get(v___x_2185_, 4);
v_newLocalDecls_2191_ = lean_ctor_get(v___x_2185_, 5);
v_newLocalDeclsForMVars_2192_ = lean_ctor_get(v___x_2185_, 6);
v_newLetDecls_2193_ = lean_ctor_get(v___x_2185_, 7);
v_nextExprIdx_2194_ = lean_ctor_get(v___x_2185_, 8);
v_exprMVarArgs_2195_ = lean_ctor_get(v___x_2185_, 9);
v_exprFVarArgs_2196_ = lean_ctor_get(v___x_2185_, 10);
v_toProcess_2197_ = lean_ctor_get(v___x_2185_, 11);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2199_ = v___x_2185_;
v_isShared_2200_ = v_isSharedCheck_2236_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_toProcess_2197_);
lean_inc(v_exprFVarArgs_2196_);
lean_inc(v_exprMVarArgs_2195_);
lean_inc(v_nextExprIdx_2194_);
lean_inc(v_newLetDecls_2193_);
lean_inc(v_newLocalDeclsForMVars_2192_);
lean_inc(v_newLocalDecls_2191_);
lean_inc(v_levelArgs_2190_);
lean_inc(v_nextLevelIdx_2189_);
lean_inc(v_levelParams_2188_);
lean_inc(v_visitedExpr_2187_);
lean_inc(v_visitedLevel_2186_);
lean_dec(v___x_2185_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2236_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; uint8_t v___x_2202_; lean_object* v___x_2204_; 
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = 0;
lean_inc(v_a_2184_);
lean_inc(v_newFVarId_2155_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 4, v_a_2184_);
lean_ctor_set(v___x_2170_, 3, v_a_2182_);
lean_ctor_set(v___x_2170_, 1, v_newFVarId_2155_);
lean_ctor_set(v___x_2170_, 0, v___x_2201_);
v___x_2204_ = v___x_2170_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_newFVarId_2155_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_userName_2165_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_a_2182_);
lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_a_2184_);
lean_ctor_set_uint8(v_reuseFailAlloc_2235_, sizeof(void*)*5, v_nondep_2168_);
v___x_2204_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*5 + 1, v___x_2202_);
v___x_2205_ = lean_array_push(v_newLetDecls_2193_, v___x_2204_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 7, v___x_2205_);
v___x_2207_ = v___x_2199_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_visitedLevel_2186_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_visitedExpr_2187_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_levelParams_2188_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v_nextLevelIdx_2189_);
lean_ctor_set(v_reuseFailAlloc_2234_, 4, v_levelArgs_2190_);
lean_ctor_set(v_reuseFailAlloc_2234_, 5, v_newLocalDecls_2191_);
lean_ctor_set(v_reuseFailAlloc_2234_, 6, v_newLocalDeclsForMVars_2192_);
lean_ctor_set(v_reuseFailAlloc_2234_, 7, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2234_, 8, v_nextExprIdx_2194_);
lean_ctor_set(v_reuseFailAlloc_2234_, 9, v_exprMVarArgs_2195_);
lean_ctor_set(v_reuseFailAlloc_2234_, 10, v_exprFVarArgs_2196_);
lean_ctor_set(v_reuseFailAlloc_2234_, 11, v_toProcess_2197_);
v___x_2207_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v_visitedLevel_2210_; lean_object* v_visitedExpr_2211_; lean_object* v_levelParams_2212_; lean_object* v_nextLevelIdx_2213_; lean_object* v_levelArgs_2214_; lean_object* v_newLocalDecls_2215_; lean_object* v_newLocalDeclsForMVars_2216_; lean_object* v_newLetDecls_2217_; lean_object* v_nextExprIdx_2218_; lean_object* v_exprMVarArgs_2219_; lean_object* v_exprFVarArgs_2220_; lean_object* v_toProcess_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2233_; 
v___x_2208_ = lean_st_ref_put(v_a_2138_, v___x_2207_);
v___x_2209_ = lean_st_ref_take(v_a_2138_);
v_visitedLevel_2210_ = lean_ctor_get(v___x_2209_, 0);
v_visitedExpr_2211_ = lean_ctor_get(v___x_2209_, 1);
v_levelParams_2212_ = lean_ctor_get(v___x_2209_, 2);
v_nextLevelIdx_2213_ = lean_ctor_get(v___x_2209_, 3);
v_levelArgs_2214_ = lean_ctor_get(v___x_2209_, 4);
v_newLocalDecls_2215_ = lean_ctor_get(v___x_2209_, 5);
v_newLocalDeclsForMVars_2216_ = lean_ctor_get(v___x_2209_, 6);
v_newLetDecls_2217_ = lean_ctor_get(v___x_2209_, 7);
v_nextExprIdx_2218_ = lean_ctor_get(v___x_2209_, 8);
v_exprMVarArgs_2219_ = lean_ctor_get(v___x_2209_, 9);
v_exprFVarArgs_2220_ = lean_ctor_get(v___x_2209_, 10);
v_toProcess_2221_ = lean_ctor_get(v___x_2209_, 11);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2223_ = v___x_2209_;
v_isShared_2224_ = v_isSharedCheck_2233_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_toProcess_2221_);
lean_inc(v_exprFVarArgs_2220_);
lean_inc(v_exprMVarArgs_2219_);
lean_inc(v_nextExprIdx_2218_);
lean_inc(v_newLetDecls_2217_);
lean_inc(v_newLocalDeclsForMVars_2216_);
lean_inc(v_newLocalDecls_2215_);
lean_inc(v_levelArgs_2214_);
lean_inc(v_nextLevelIdx_2213_);
lean_inc(v_levelParams_2212_);
lean_inc(v_visitedExpr_2211_);
lean_inc(v_visitedLevel_2210_);
lean_dec(v___x_2209_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2233_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
size_t v_sz_2225_; size_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v_sz_2225_ = lean_array_size(v_newLocalDecls_2215_);
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2155_, v_a_2184_, v_sz_2225_, v___x_2226_, v_newLocalDecls_2215_);
lean_dec(v_a_2184_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 5, v___x_2227_);
v___x_2229_ = v___x_2223_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_visitedLevel_2210_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_visitedExpr_2211_);
lean_ctor_set(v_reuseFailAlloc_2232_, 2, v_levelParams_2212_);
lean_ctor_set(v_reuseFailAlloc_2232_, 3, v_nextLevelIdx_2213_);
lean_ctor_set(v_reuseFailAlloc_2232_, 4, v_levelArgs_2214_);
lean_ctor_set(v_reuseFailAlloc_2232_, 5, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2232_, 6, v_newLocalDeclsForMVars_2216_);
lean_ctor_set(v_reuseFailAlloc_2232_, 7, v_newLetDecls_2217_);
lean_ctor_set(v_reuseFailAlloc_2232_, 8, v_nextExprIdx_2218_);
lean_ctor_set(v_reuseFailAlloc_2232_, 9, v_exprMVarArgs_2219_);
lean_ctor_set(v_reuseFailAlloc_2232_, 10, v_exprFVarArgs_2220_);
lean_ctor_set(v_reuseFailAlloc_2232_, 11, v_toProcess_2221_);
v___x_2229_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_st_ref_put(v_a_2138_, v___x_2229_);
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec(v_a_2182_);
lean_del_object(v___x_2170_);
lean_dec(v_userName_2165_);
lean_dec(v_newFVarId_2155_);
v_a_2237_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2183_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2183_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_del_object(v___x_2170_);
lean_dec_ref(v_value_2167_);
lean_dec(v_userName_2165_);
lean_dec(v_newFVarId_2155_);
v_a_2245_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2181_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2181_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
else
{
lean_dec(v_a_2173_);
lean_del_object(v___x_2170_);
lean_dec_ref(v_value_2167_);
goto v___jp_2174_;
}
v___jp_2174_:
{
uint8_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = 0;
v___x_2176_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2155_, v_userName_2165_, v_type_2166_, v___x_2175_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_dec_ref_known(v___x_2176_, 1);
v___x_2177_ = l_Lean_mkFVar(v_fvarId_2154_);
v___x_2178_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2177_, v_a_2138_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_dec_ref_known(v___x_2178_, 1);
goto _start;
}
else
{
return v___x_2178_;
}
}
else
{
lean_dec(v_fvarId_2154_);
return v___x_2176_;
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_del_object(v___x_2170_);
lean_dec_ref(v_value_2167_);
lean_dec_ref(v_type_2166_);
lean_dec(v_userName_2165_);
lean_dec(v_newFVarId_2155_);
lean_dec(v_fvarId_2154_);
v_a_2253_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2172_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2172_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_newFVarId_2155_);
lean_dec(v_fvarId_2154_);
v_a_2264_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2156_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2156_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
v_a_2273_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2144_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2144_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Meta_Closure_process(v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
return v_res_2288_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(lean_object* v_00_u03b2_2289_, lean_object* v_k_2290_, lean_object* v_t_2291_){
_start:
{
uint8_t v___x_2292_; 
v___x_2292_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2290_, v_t_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___boxed(lean_object* v_00_u03b2_2293_, lean_object* v_k_2294_, lean_object* v_t_2295_){
_start:
{
uint8_t v_res_2296_; lean_object* v_r_2297_; 
v_res_2296_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(v_00_u03b2_2293_, v_k_2294_, v_t_2295_);
lean_dec(v_t_2295_);
lean_dec(v_k_2294_);
v_r_2297_ = lean_box(v_res_2296_);
return v_r_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object* v_decls_2298_, lean_object* v_xs_2299_, uint8_t v_isLambda_2300_, lean_object* v_i_2301_, lean_object* v_x_2302_, lean_object* v_b_2303_){
_start:
{
lean_object* v_decl_2304_; 
v_decl_2304_ = lean_array_fget_borrowed(v_decls_2298_, v_i_2301_);
if (lean_obj_tag(v_decl_2304_) == 0)
{
lean_object* v_userName_2305_; lean_object* v_type_2306_; uint8_t v_bi_2307_; lean_object* v_ty_2308_; 
v_userName_2305_ = lean_ctor_get(v_decl_2304_, 2);
v_type_2306_ = lean_ctor_get(v_decl_2304_, 3);
v_bi_2307_ = lean_ctor_get_uint8(v_decl_2304_, sizeof(void*)*4);
v_ty_2308_ = lean_expr_abstract_range(v_type_2306_, v_i_2301_, v_xs_2299_);
if (v_isLambda_2300_ == 0)
{
lean_object* v___x_2309_; 
lean_inc(v_userName_2305_);
v___x_2309_ = l_Lean_mkForall(v_userName_2305_, v_bi_2307_, v_ty_2308_, v_b_2303_);
return v___x_2309_;
}
else
{
lean_object* v___x_2310_; 
lean_inc(v_userName_2305_);
v___x_2310_ = l_Lean_mkLambda(v_userName_2305_, v_bi_2307_, v_ty_2308_, v_b_2303_);
return v___x_2310_;
}
}
else
{
lean_object* v_userName_2311_; lean_object* v_type_2312_; lean_object* v_value_2313_; uint8_t v_nondep_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v_userName_2311_ = lean_ctor_get(v_decl_2304_, 2);
v_type_2312_ = lean_ctor_get(v_decl_2304_, 3);
v_value_2313_ = lean_ctor_get(v_decl_2304_, 4);
v_nondep_2314_ = lean_ctor_get_uint8(v_decl_2304_, sizeof(void*)*5);
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = lean_expr_has_loose_bvar(v_b_2303_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_expr_lower_loose_bvars(v_b_2303_, v___x_2317_, v___x_2317_);
lean_dec_ref(v_b_2303_);
return v___x_2318_;
}
else
{
lean_object* v_ty_2319_; lean_object* v_val_2320_; lean_object* v___x_2321_; 
v_ty_2319_ = lean_expr_abstract_range(v_type_2312_, v_i_2301_, v_xs_2299_);
v_val_2320_ = lean_expr_abstract_range(v_value_2313_, v_i_2301_, v_xs_2299_);
lean_inc(v_userName_2311_);
v___x_2321_ = l_Lean_Expr_letE___override(v_userName_2311_, v_ty_2319_, v_val_2320_, v_b_2303_, v_nondep_2314_);
return v___x_2321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object* v_decls_2322_, lean_object* v_xs_2323_, lean_object* v_isLambda_2324_, lean_object* v_i_2325_, lean_object* v_x_2326_, lean_object* v_b_2327_){
_start:
{
uint8_t v_isLambda_boxed_2328_; lean_object* v_res_2329_; 
v_isLambda_boxed_2328_ = lean_unbox(v_isLambda_2324_);
v_res_2329_ = l_Lean_Meta_Closure_mkBinding___lam__0(v_decls_2322_, v_xs_2323_, v_isLambda_boxed_2328_, v_i_2325_, v_x_2326_, v_b_2327_);
lean_dec(v_i_2325_);
lean_dec_ref(v_xs_2323_);
lean_dec_ref(v_decls_2322_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t v_isLambda_2350_, lean_object* v_decls_2351_, lean_object* v_b_2352_){
_start:
{
lean_object* v___f_2353_; lean_object* v___x_2354_; size_t v_sz_2355_; size_t v___x_2356_; lean_object* v_xs_2357_; lean_object* v___x_2358_; lean_object* v___f_2359_; lean_object* v_b_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___f_2353_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__0));
v___x_2354_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__10));
v_sz_2355_ = lean_array_size(v_decls_2351_);
v___x_2356_ = ((size_t)0ULL);
lean_inc_ref_n(v_decls_2351_, 2);
v_xs_2357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2354_, v___f_2353_, v_sz_2355_, v___x_2356_, v_decls_2351_);
v___x_2358_ = lean_box(v_isLambda_2350_);
lean_inc(v_xs_2357_);
v___f_2359_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2359_, 0, v_decls_2351_);
lean_closure_set(v___f_2359_, 1, v_xs_2357_);
lean_closure_set(v___f_2359_, 2, v___x_2358_);
v_b_2360_ = lean_expr_abstract(v_b_2352_, v_xs_2357_);
lean_dec(v_xs_2357_);
v___x_2361_ = lean_array_get_size(v_decls_2351_);
lean_dec_ref(v_decls_2351_);
v___x_2362_ = l_Nat_foldRev___redArg(v___x_2361_, v___f_2359_, v_b_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* v_isLambda_2363_, lean_object* v_decls_2364_, lean_object* v_b_2365_){
_start:
{
uint8_t v_isLambda_boxed_2366_; lean_object* v_res_2367_; 
v_isLambda_boxed_2366_ = lean_unbox(v_isLambda_2363_);
v_res_2367_ = l_Lean_Meta_Closure_mkBinding(v_isLambda_boxed_2366_, v_decls_2364_, v_b_2365_);
lean_dec_ref(v_b_2365_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(size_t v_sz_2368_, size_t v_i_2369_, lean_object* v_bs_2370_){
_start:
{
uint8_t v___x_2371_; 
v___x_2371_ = lean_usize_dec_lt(v_i_2369_, v_sz_2368_);
if (v___x_2371_ == 0)
{
return v_bs_2370_;
}
else
{
lean_object* v_v_2372_; lean_object* v___x_2373_; lean_object* v_bs_x27_2374_; lean_object* v___x_2375_; size_t v___x_2376_; size_t v___x_2377_; lean_object* v___x_2378_; 
v_v_2372_ = lean_array_uget(v_bs_2370_, v_i_2369_);
v___x_2373_ = lean_unsigned_to_nat(0u);
v_bs_x27_2374_ = lean_array_uset(v_bs_2370_, v_i_2369_, v___x_2373_);
v___x_2375_ = l_Lean_LocalDecl_toExpr(v_v_2372_);
v___x_2376_ = ((size_t)1ULL);
v___x_2377_ = lean_usize_add(v_i_2369_, v___x_2376_);
v___x_2378_ = lean_array_uset(v_bs_x27_2374_, v_i_2369_, v___x_2375_);
v_i_2369_ = v___x_2377_;
v_bs_2370_ = v___x_2378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object* v_sz_2380_, lean_object* v_i_2381_, lean_object* v_bs_2382_){
_start:
{
size_t v_sz_boxed_2383_; size_t v_i_boxed_2384_; lean_object* v_res_2385_; 
v_sz_boxed_2383_ = lean_unbox_usize(v_sz_2380_);
lean_dec(v_sz_2380_);
v_i_boxed_2384_ = lean_unbox_usize(v_i_2381_);
lean_dec(v_i_2381_);
v_res_2385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_boxed_2383_, v_i_boxed_2384_, v_bs_2382_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object* v_decls_2386_, lean_object* v_xs_2387_, lean_object* v_x_2388_, lean_object* v_x_2389_){
_start:
{
lean_object* v_zero_2390_; uint8_t v_isZero_2391_; 
v_zero_2390_ = lean_unsigned_to_nat(0u);
v_isZero_2391_ = lean_nat_dec_eq(v_x_2388_, v_zero_2390_);
if (v_isZero_2391_ == 1)
{
lean_dec(v_x_2388_);
return v_x_2389_;
}
else
{
lean_object* v_one_2392_; lean_object* v_n_2393_; lean_object* v_decl_2394_; 
v_one_2392_ = lean_unsigned_to_nat(1u);
v_n_2393_ = lean_nat_sub(v_x_2388_, v_one_2392_);
lean_dec(v_x_2388_);
v_decl_2394_ = lean_array_fget_borrowed(v_decls_2386_, v_n_2393_);
if (lean_obj_tag(v_decl_2394_) == 0)
{
lean_object* v_userName_2395_; lean_object* v_type_2396_; uint8_t v_bi_2397_; lean_object* v_ty_2398_; lean_object* v___x_2399_; 
v_userName_2395_ = lean_ctor_get(v_decl_2394_, 2);
v_type_2396_ = lean_ctor_get(v_decl_2394_, 3);
v_bi_2397_ = lean_ctor_get_uint8(v_decl_2394_, sizeof(void*)*4);
v_ty_2398_ = lean_expr_abstract_range(v_type_2396_, v_n_2393_, v_xs_2387_);
lean_inc(v_userName_2395_);
v___x_2399_ = l_Lean_mkLambda(v_userName_2395_, v_bi_2397_, v_ty_2398_, v_x_2389_);
v_x_2388_ = v_n_2393_;
v_x_2389_ = v___x_2399_;
goto _start;
}
else
{
lean_object* v_userName_2401_; lean_object* v_type_2402_; lean_object* v_value_2403_; uint8_t v_nondep_2404_; uint8_t v___x_2405_; 
v_userName_2401_ = lean_ctor_get(v_decl_2394_, 2);
v_type_2402_ = lean_ctor_get(v_decl_2394_, 3);
v_value_2403_ = lean_ctor_get(v_decl_2394_, 4);
v_nondep_2404_ = lean_ctor_get_uint8(v_decl_2394_, sizeof(void*)*5);
v___x_2405_ = lean_expr_has_loose_bvar(v_x_2389_, v_zero_2390_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_expr_lower_loose_bvars(v_x_2389_, v_one_2392_, v_one_2392_);
lean_dec_ref(v_x_2389_);
v_x_2388_ = v_n_2393_;
v_x_2389_ = v___x_2406_;
goto _start;
}
else
{
lean_object* v_ty_2408_; lean_object* v_val_2409_; lean_object* v___x_2410_; 
v_ty_2408_ = lean_expr_abstract_range(v_type_2402_, v_n_2393_, v_xs_2387_);
v_val_2409_ = lean_expr_abstract_range(v_value_2403_, v_n_2393_, v_xs_2387_);
lean_inc(v_userName_2401_);
v___x_2410_ = l_Lean_Expr_letE___override(v_userName_2401_, v_ty_2408_, v_val_2409_, v_x_2389_, v_nondep_2404_);
v_x_2388_ = v_n_2393_;
v_x_2389_ = v___x_2410_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1___boxed(lean_object* v_decls_2412_, lean_object* v_xs_2413_, lean_object* v_x_2414_, lean_object* v_x_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2412_, v_xs_2413_, v_x_2414_, v_x_2415_);
lean_dec_ref(v_xs_2413_);
lean_dec_ref(v_decls_2412_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(lean_object* v_decls_2417_, lean_object* v_xs_2418_, lean_object* v_x_2419_, lean_object* v_x_2420_){
_start:
{
lean_object* v_zero_2421_; uint8_t v_isZero_2422_; 
v_zero_2421_ = lean_unsigned_to_nat(0u);
v_isZero_2422_ = lean_nat_dec_eq(v_x_2419_, v_zero_2421_);
if (v_isZero_2422_ == 1)
{
return v_x_2420_;
}
else
{
lean_object* v_one_2423_; lean_object* v_n_2424_; lean_object* v_decl_2425_; 
v_one_2423_ = lean_unsigned_to_nat(1u);
v_n_2424_ = lean_nat_sub(v_x_2419_, v_one_2423_);
v_decl_2425_ = lean_array_fget_borrowed(v_decls_2417_, v_n_2424_);
if (lean_obj_tag(v_decl_2425_) == 0)
{
lean_object* v_userName_2426_; lean_object* v_type_2427_; uint8_t v_bi_2428_; lean_object* v_ty_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_userName_2426_ = lean_ctor_get(v_decl_2425_, 2);
v_type_2427_ = lean_ctor_get(v_decl_2425_, 3);
v_bi_2428_ = lean_ctor_get_uint8(v_decl_2425_, sizeof(void*)*4);
v_ty_2429_ = lean_expr_abstract_range(v_type_2427_, v_n_2424_, v_xs_2418_);
lean_inc(v_userName_2426_);
v___x_2430_ = l_Lean_mkLambda(v_userName_2426_, v_bi_2428_, v_ty_2429_, v_x_2420_);
v___x_2431_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2417_, v_xs_2418_, v_n_2424_, v___x_2430_);
return v___x_2431_;
}
else
{
lean_object* v_userName_2432_; lean_object* v_type_2433_; lean_object* v_value_2434_; uint8_t v_nondep_2435_; uint8_t v___x_2436_; 
v_userName_2432_ = lean_ctor_get(v_decl_2425_, 2);
v_type_2433_ = lean_ctor_get(v_decl_2425_, 3);
v_value_2434_ = lean_ctor_get(v_decl_2425_, 4);
v_nondep_2435_ = lean_ctor_get_uint8(v_decl_2425_, sizeof(void*)*5);
v___x_2436_ = lean_expr_has_loose_bvar(v_x_2420_, v_zero_2421_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_expr_lower_loose_bvars(v_x_2420_, v_one_2423_, v_one_2423_);
lean_dec_ref(v_x_2420_);
v___x_2438_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2417_, v_xs_2418_, v_n_2424_, v___x_2437_);
return v___x_2438_;
}
else
{
lean_object* v_ty_2439_; lean_object* v_val_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_ty_2439_ = lean_expr_abstract_range(v_type_2433_, v_n_2424_, v_xs_2418_);
v_val_2440_ = lean_expr_abstract_range(v_value_2434_, v_n_2424_, v_xs_2418_);
lean_inc(v_userName_2432_);
v___x_2441_ = l_Lean_Expr_letE___override(v_userName_2432_, v_ty_2439_, v_val_2440_, v_x_2420_, v_nondep_2435_);
v___x_2442_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2417_, v_xs_2418_, v_n_2424_, v___x_2441_);
return v___x_2442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object* v_decls_2443_, lean_object* v_xs_2444_, lean_object* v_x_2445_, lean_object* v_x_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2443_, v_xs_2444_, v_x_2445_, v_x_2446_);
lean_dec(v_x_2445_);
lean_dec_ref(v_xs_2444_);
lean_dec_ref(v_decls_2443_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* v_decls_2448_, lean_object* v_b_2449_){
_start:
{
size_t v_sz_2450_; size_t v___x_2451_; lean_object* v_xs_2452_; lean_object* v_b_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_sz_2450_ = lean_array_size(v_decls_2448_);
v___x_2451_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2448_);
v_xs_2452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2450_, v___x_2451_, v_decls_2448_);
v_b_2453_ = lean_expr_abstract(v_b_2449_, v_xs_2452_);
v___x_2454_ = lean_array_get_size(v_decls_2448_);
v___x_2455_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2448_, v_xs_2452_, v___x_2454_, v_b_2453_);
lean_dec_ref(v_xs_2452_);
lean_dec_ref(v_decls_2448_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* v_decls_2456_, lean_object* v_b_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_Meta_Closure_mkLambda(v_decls_2456_, v_b_2457_);
lean_dec_ref(v_b_2457_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(lean_object* v_decls_2459_, lean_object* v_xs_2460_, lean_object* v_x_2461_, lean_object* v_x_2462_){
_start:
{
lean_object* v_zero_2463_; uint8_t v_isZero_2464_; 
v_zero_2463_ = lean_unsigned_to_nat(0u);
v_isZero_2464_ = lean_nat_dec_eq(v_x_2461_, v_zero_2463_);
if (v_isZero_2464_ == 1)
{
lean_dec(v_x_2461_);
return v_x_2462_;
}
else
{
lean_object* v_one_2465_; lean_object* v_n_2466_; lean_object* v_decl_2467_; 
v_one_2465_ = lean_unsigned_to_nat(1u);
v_n_2466_ = lean_nat_sub(v_x_2461_, v_one_2465_);
lean_dec(v_x_2461_);
v_decl_2467_ = lean_array_fget_borrowed(v_decls_2459_, v_n_2466_);
if (lean_obj_tag(v_decl_2467_) == 0)
{
lean_object* v_userName_2468_; lean_object* v_type_2469_; uint8_t v_bi_2470_; lean_object* v_ty_2471_; lean_object* v___x_2472_; 
v_userName_2468_ = lean_ctor_get(v_decl_2467_, 2);
v_type_2469_ = lean_ctor_get(v_decl_2467_, 3);
v_bi_2470_ = lean_ctor_get_uint8(v_decl_2467_, sizeof(void*)*4);
v_ty_2471_ = lean_expr_abstract_range(v_type_2469_, v_n_2466_, v_xs_2460_);
lean_inc(v_userName_2468_);
v___x_2472_ = l_Lean_mkForall(v_userName_2468_, v_bi_2470_, v_ty_2471_, v_x_2462_);
v_x_2461_ = v_n_2466_;
v_x_2462_ = v___x_2472_;
goto _start;
}
else
{
lean_object* v_userName_2474_; lean_object* v_type_2475_; lean_object* v_value_2476_; uint8_t v_nondep_2477_; uint8_t v___x_2478_; 
v_userName_2474_ = lean_ctor_get(v_decl_2467_, 2);
v_type_2475_ = lean_ctor_get(v_decl_2467_, 3);
v_value_2476_ = lean_ctor_get(v_decl_2467_, 4);
v_nondep_2477_ = lean_ctor_get_uint8(v_decl_2467_, sizeof(void*)*5);
v___x_2478_ = lean_expr_has_loose_bvar(v_x_2462_, v_zero_2463_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_expr_lower_loose_bvars(v_x_2462_, v_one_2465_, v_one_2465_);
lean_dec_ref(v_x_2462_);
v_x_2461_ = v_n_2466_;
v_x_2462_ = v___x_2479_;
goto _start;
}
else
{
lean_object* v_ty_2481_; lean_object* v_val_2482_; lean_object* v___x_2483_; 
v_ty_2481_ = lean_expr_abstract_range(v_type_2475_, v_n_2466_, v_xs_2460_);
v_val_2482_ = lean_expr_abstract_range(v_value_2476_, v_n_2466_, v_xs_2460_);
lean_inc(v_userName_2474_);
v___x_2483_ = l_Lean_Expr_letE___override(v_userName_2474_, v_ty_2481_, v_val_2482_, v_x_2462_, v_nondep_2477_);
v_x_2461_ = v_n_2466_;
v_x_2462_ = v___x_2483_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0___boxed(lean_object* v_decls_2485_, lean_object* v_xs_2486_, lean_object* v_x_2487_, lean_object* v_x_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2485_, v_xs_2486_, v_x_2487_, v_x_2488_);
lean_dec_ref(v_xs_2486_);
lean_dec_ref(v_decls_2485_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(lean_object* v_decls_2490_, lean_object* v_xs_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_){
_start:
{
lean_object* v_zero_2494_; uint8_t v_isZero_2495_; 
v_zero_2494_ = lean_unsigned_to_nat(0u);
v_isZero_2495_ = lean_nat_dec_eq(v_x_2492_, v_zero_2494_);
if (v_isZero_2495_ == 1)
{
return v_x_2493_;
}
else
{
lean_object* v_one_2496_; lean_object* v_n_2497_; lean_object* v_decl_2498_; 
v_one_2496_ = lean_unsigned_to_nat(1u);
v_n_2497_ = lean_nat_sub(v_x_2492_, v_one_2496_);
v_decl_2498_ = lean_array_fget_borrowed(v_decls_2490_, v_n_2497_);
if (lean_obj_tag(v_decl_2498_) == 0)
{
lean_object* v_userName_2499_; lean_object* v_type_2500_; uint8_t v_bi_2501_; lean_object* v_ty_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_userName_2499_ = lean_ctor_get(v_decl_2498_, 2);
v_type_2500_ = lean_ctor_get(v_decl_2498_, 3);
v_bi_2501_ = lean_ctor_get_uint8(v_decl_2498_, sizeof(void*)*4);
v_ty_2502_ = lean_expr_abstract_range(v_type_2500_, v_n_2497_, v_xs_2491_);
lean_inc(v_userName_2499_);
v___x_2503_ = l_Lean_mkForall(v_userName_2499_, v_bi_2501_, v_ty_2502_, v_x_2493_);
v___x_2504_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2490_, v_xs_2491_, v_n_2497_, v___x_2503_);
return v___x_2504_;
}
else
{
lean_object* v_userName_2505_; lean_object* v_type_2506_; lean_object* v_value_2507_; uint8_t v_nondep_2508_; uint8_t v___x_2509_; 
v_userName_2505_ = lean_ctor_get(v_decl_2498_, 2);
v_type_2506_ = lean_ctor_get(v_decl_2498_, 3);
v_value_2507_ = lean_ctor_get(v_decl_2498_, 4);
v_nondep_2508_ = lean_ctor_get_uint8(v_decl_2498_, sizeof(void*)*5);
v___x_2509_ = lean_expr_has_loose_bvar(v_x_2493_, v_zero_2494_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = lean_expr_lower_loose_bvars(v_x_2493_, v_one_2496_, v_one_2496_);
lean_dec_ref(v_x_2493_);
v___x_2511_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2490_, v_xs_2491_, v_n_2497_, v___x_2510_);
return v___x_2511_;
}
else
{
lean_object* v_ty_2512_; lean_object* v_val_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_ty_2512_ = lean_expr_abstract_range(v_type_2506_, v_n_2497_, v_xs_2491_);
v_val_2513_ = lean_expr_abstract_range(v_value_2507_, v_n_2497_, v_xs_2491_);
lean_inc(v_userName_2505_);
v___x_2514_ = l_Lean_Expr_letE___override(v_userName_2505_, v_ty_2512_, v_val_2513_, v_x_2493_, v_nondep_2508_);
v___x_2515_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2490_, v_xs_2491_, v_n_2497_, v___x_2514_);
return v___x_2515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object* v_decls_2516_, lean_object* v_xs_2517_, lean_object* v_x_2518_, lean_object* v_x_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2516_, v_xs_2517_, v_x_2518_, v_x_2519_);
lean_dec(v_x_2518_);
lean_dec_ref(v_xs_2517_);
lean_dec_ref(v_decls_2516_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* v_decls_2521_, lean_object* v_b_2522_){
_start:
{
size_t v_sz_2523_; size_t v___x_2524_; lean_object* v_xs_2525_; lean_object* v_b_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v_sz_2523_ = lean_array_size(v_decls_2521_);
v___x_2524_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2521_);
v_xs_2525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2523_, v___x_2524_, v_decls_2521_);
v_b_2526_ = lean_expr_abstract(v_b_2522_, v_xs_2525_);
v___x_2527_ = lean_array_get_size(v_decls_2521_);
v___x_2528_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2521_, v_xs_2525_, v___x_2527_, v_b_2526_);
lean_dec_ref(v_xs_2525_);
lean_dec_ref(v_decls_2521_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* v_decls_2529_, lean_object* v_b_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_Meta_Closure_mkForall(v_decls_2529_, v_b_2530_);
lean_dec_ref(v_b_2530_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object* v_a_2532_, lean_object* v_cache_2533_, lean_object* v_a_x3f_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v_mctx_2537_; lean_object* v_zetaDeltaFVarIds_2538_; lean_object* v_postponed_2539_; lean_object* v_diag_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2550_; 
v___x_2536_ = lean_st_ref_take(v_a_2532_);
v_mctx_2537_ = lean_ctor_get(v___x_2536_, 0);
v_zetaDeltaFVarIds_2538_ = lean_ctor_get(v___x_2536_, 2);
v_postponed_2539_ = lean_ctor_get(v___x_2536_, 3);
v_diag_2540_ = lean_ctor_get(v___x_2536_, 4);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2550_ == 0)
{
lean_object* v_unused_2551_; 
v_unused_2551_ = lean_ctor_get(v___x_2536_, 1);
lean_dec(v_unused_2551_);
v___x_2542_ = v___x_2536_;
v_isShared_2543_ = v_isSharedCheck_2550_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_diag_2540_);
lean_inc(v_postponed_2539_);
lean_inc(v_zetaDeltaFVarIds_2538_);
lean_inc(v_mctx_2537_);
lean_dec(v___x_2536_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2550_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2544_ = lean_box(0);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 1, v_cache_2533_);
v___x_2546_ = v___x_2542_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_mctx_2537_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_cache_2533_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v_zetaDeltaFVarIds_2538_);
lean_ctor_set(v_reuseFailAlloc_2549_, 3, v_postponed_2539_);
lean_ctor_set(v_reuseFailAlloc_2549_, 4, v_diag_2540_);
v___x_2546_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = lean_st_ref_put(v_a_2532_, v___x_2546_);
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2544_);
return v___x_2548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object* v_a_2552_, lean_object* v_cache_2553_, lean_object* v_a_x3f_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2552_, v_cache_2553_, v_a_x3f_2554_);
lean_dec(v_a_x3f_2554_);
lean_dec(v_a_2552_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object* v_a_2557_, lean_object* v_zetaDeltaFVarIds_2558_, lean_object* v_a_x3f_2559_){
_start:
{
lean_object* v___x_2561_; lean_object* v_mctx_2562_; lean_object* v_cache_2563_; lean_object* v_postponed_2564_; lean_object* v_diag_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2575_; 
v___x_2561_ = lean_st_ref_take(v_a_2557_);
v_mctx_2562_ = lean_ctor_get(v___x_2561_, 0);
v_cache_2563_ = lean_ctor_get(v___x_2561_, 1);
v_postponed_2564_ = lean_ctor_get(v___x_2561_, 3);
v_diag_2565_ = lean_ctor_get(v___x_2561_, 4);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v___x_2561_, 2);
lean_dec(v_unused_2576_);
v___x_2567_ = v___x_2561_;
v_isShared_2568_ = v_isSharedCheck_2575_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_diag_2565_);
lean_inc(v_postponed_2564_);
lean_inc(v_cache_2563_);
lean_inc(v_mctx_2562_);
lean_dec(v___x_2561_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2575_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = lean_box(0);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 2, v_zetaDeltaFVarIds_2558_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_mctx_2562_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_cache_2563_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v_zetaDeltaFVarIds_2558_);
lean_ctor_set(v_reuseFailAlloc_2574_, 3, v_postponed_2564_);
lean_ctor_set(v_reuseFailAlloc_2574_, 4, v_diag_2565_);
v___x_2571_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = lean_st_ref_put(v_a_2557_, v___x_2571_);
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2569_);
return v___x_2573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object* v_a_2577_, lean_object* v_zetaDeltaFVarIds_2578_, lean_object* v_a_x3f_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2577_, v_zetaDeltaFVarIds_2578_, v_a_x3f_2579_);
lean_dec(v_a_x3f_2579_);
lean_dec(v_a_2577_);
return v_res_2581_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2582_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__0);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__1);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg();
return v_res_2588_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0(void){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg();
return v___x_2589_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1(void){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__0);
v___x_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
return v___x_2591_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
return v___x_2593_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__3(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2595_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_2596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
lean_ctor_set(v___x_2596_, 2, v___x_2594_);
return v___x_2596_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__4(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2597_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__3, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__3_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__3);
v___x_2598_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2);
v___x_2599_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_2600_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_2601_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v___x_2599_);
lean_ctor_set(v___x_2601_, 2, v___x_2598_);
lean_ctor_set(v___x_2601_, 3, v___x_2599_);
lean_ctor_set(v___x_2601_, 4, v___x_2599_);
lean_ctor_set(v___x_2601_, 5, v___x_2599_);
lean_ctor_set(v___x_2601_, 6, v___x_2599_);
lean_ctor_set(v___x_2601_, 7, v___x_2597_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* v_type_2602_, lean_object* v_value_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v_cache_2613_; lean_object* v_a_2615_; lean_object* v___x_2626_; lean_object* v_mctx_2627_; lean_object* v_zetaDeltaFVarIds_2628_; lean_object* v_postponed_2629_; lean_object* v_diag_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2696_; 
v___x_2611_ = lean_box(1);
v___x_2612_ = lean_st_ref_get(v_a_2607_);
v_cache_2613_ = lean_ctor_get(v___x_2612_, 1);
lean_inc_ref(v_cache_2613_);
lean_dec(v___x_2612_);
v___x_2626_ = lean_st_ref_take(v_a_2607_);
v_mctx_2627_ = lean_ctor_get(v___x_2626_, 0);
v_zetaDeltaFVarIds_2628_ = lean_ctor_get(v___x_2626_, 2);
v_postponed_2629_ = lean_ctor_get(v___x_2626_, 3);
v_diag_2630_ = lean_ctor_get(v___x_2626_, 4);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v___x_2626_, 1);
lean_dec(v_unused_2697_);
v___x_2632_ = v___x_2626_;
v_isShared_2633_ = v_isSharedCheck_2696_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_diag_2630_);
lean_inc(v_postponed_2629_);
lean_inc(v_zetaDeltaFVarIds_2628_);
lean_inc(v_mctx_2627_);
lean_dec(v___x_2626_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2696_;
goto v_resetjp_2631_;
}
v___jp_2614_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
v___x_2616_ = lean_box(0);
v___x_2617_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2607_, v_cache_2613_, v___x_2616_);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2624_ == 0)
{
lean_object* v_unused_2625_; 
v_unused_2625_ = lean_ctor_get(v___x_2617_, 0);
lean_dec(v_unused_2625_);
v___x_2619_ = v___x_2617_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_dec(v___x_2617_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set_tag(v___x_2619_, 1);
lean_ctor_set(v___x_2619_, 0, v_a_2615_);
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2615_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2634_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__4, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__4_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__4);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 1, v___x_2634_);
v___x_2636_ = v___x_2632_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_mctx_2627_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2695_, 2, v_zetaDeltaFVarIds_2628_);
lean_ctor_set(v_reuseFailAlloc_2695_, 3, v_postponed_2629_);
lean_ctor_set(v_reuseFailAlloc_2695_, 4, v_diag_2630_);
v___x_2636_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_object* v___x_2637_; lean_object* v_keyedConfig_2638_; lean_object* v_zetaDeltaSet_2639_; lean_object* v_lctx_2640_; lean_object* v_localInstances_2641_; lean_object* v_defEqCtx_x3f_2642_; lean_object* v_synthPendingDepth_2643_; lean_object* v_customCanUnfoldPredicate_x3f_2644_; uint8_t v_univApprox_2645_; uint8_t v_inTypeClassResolution_2646_; uint8_t v_cacheInferType_2647_; uint8_t v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v_mctx_2651_; lean_object* v_cache_2652_; lean_object* v_zetaDeltaFVarIds_2653_; lean_object* v_postponed_2654_; lean_object* v_diag_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2694_; 
v___x_2637_ = lean_st_ref_put(v_a_2607_, v___x_2636_);
v_keyedConfig_2638_ = lean_ctor_get(v_a_2606_, 0);
v_zetaDeltaSet_2639_ = lean_ctor_get(v_a_2606_, 1);
v_lctx_2640_ = lean_ctor_get(v_a_2606_, 2);
v_localInstances_2641_ = lean_ctor_get(v_a_2606_, 3);
v_defEqCtx_x3f_2642_ = lean_ctor_get(v_a_2606_, 4);
v_synthPendingDepth_2643_ = lean_ctor_get(v_a_2606_, 5);
v_customCanUnfoldPredicate_x3f_2644_ = lean_ctor_get(v_a_2606_, 6);
v_univApprox_2645_ = lean_ctor_get_uint8(v_a_2606_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2646_ = lean_ctor_get_uint8(v_a_2606_, sizeof(void*)*7 + 2);
v_cacheInferType_2647_ = lean_ctor_get_uint8(v_a_2606_, sizeof(void*)*7 + 3);
v___x_2648_ = 1;
lean_inc(v_customCanUnfoldPredicate_x3f_2644_);
lean_inc(v_synthPendingDepth_2643_);
lean_inc(v_defEqCtx_x3f_2642_);
lean_inc_ref(v_localInstances_2641_);
lean_inc_ref(v_lctx_2640_);
lean_inc(v_zetaDeltaSet_2639_);
lean_inc_ref(v_keyedConfig_2638_);
v___x_2649_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2649_, 0, v_keyedConfig_2638_);
lean_ctor_set(v___x_2649_, 1, v_zetaDeltaSet_2639_);
lean_ctor_set(v___x_2649_, 2, v_lctx_2640_);
lean_ctor_set(v___x_2649_, 3, v_localInstances_2641_);
lean_ctor_set(v___x_2649_, 4, v_defEqCtx_x3f_2642_);
lean_ctor_set(v___x_2649_, 5, v_synthPendingDepth_2643_);
lean_ctor_set(v___x_2649_, 6, v_customCanUnfoldPredicate_x3f_2644_);
lean_ctor_set_uint8(v___x_2649_, sizeof(void*)*7, v___x_2648_);
lean_ctor_set_uint8(v___x_2649_, sizeof(void*)*7 + 1, v_univApprox_2645_);
lean_ctor_set_uint8(v___x_2649_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2646_);
lean_ctor_set_uint8(v___x_2649_, sizeof(void*)*7 + 3, v_cacheInferType_2647_);
v___x_2650_ = lean_st_ref_take(v_a_2607_);
v_mctx_2651_ = lean_ctor_get(v___x_2650_, 0);
v_cache_2652_ = lean_ctor_get(v___x_2650_, 1);
v_zetaDeltaFVarIds_2653_ = lean_ctor_get(v___x_2650_, 2);
v_postponed_2654_ = lean_ctor_get(v___x_2650_, 3);
v_diag_2655_ = lean_ctor_get(v___x_2650_, 4);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2657_ = v___x_2650_;
v_isShared_2658_ = v_isSharedCheck_2694_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_diag_2655_);
lean_inc(v_postponed_2654_);
lean_inc(v_zetaDeltaFVarIds_2653_);
lean_inc(v_cache_2652_);
lean_inc(v_mctx_2651_);
lean_dec(v___x_2650_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2694_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_a_2660_; lean_object* v___x_2664_; 
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 2, v___x_2611_);
v___x_2664_ = v___x_2657_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_mctx_2651_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_cache_2652_);
lean_ctor_set(v_reuseFailAlloc_2693_, 2, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2693_, 3, v_postponed_2654_);
lean_ctor_set(v_reuseFailAlloc_2693_, 4, v_diag_2655_);
v___x_2664_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2663_;
}
v___jp_2659_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = lean_box(0);
v___x_2662_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2607_, v_zetaDeltaFVarIds_2653_, v___x_2661_);
lean_dec_ref(v___x_2662_);
v_a_2615_ = v_a_2660_;
goto v___jp_2614_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = lean_st_ref_put(v_a_2607_, v___x_2664_);
v___x_2666_ = l_Lean_Meta_Closure_collectExpr(v_type_2602_, v_a_2604_, v_a_2605_, v___x_2649_, v_a_2607_, v_a_2608_, v_a_2609_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2668_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2666_, 1);
v___x_2668_ = l_Lean_Meta_Closure_collectExpr(v_value_2603_, v_a_2604_, v_a_2605_, v___x_2649_, v_a_2607_, v_a_2608_, v_a_2609_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2670_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2668_, 1);
v___x_2670_ = l_Lean_Meta_Closure_process(v_a_2604_, v_a_2605_, v___x_2649_, v_a_2607_, v_a_2608_, v_a_2609_);
lean_dec_ref_known(v___x_2649_, 7);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2688_; 
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v___x_2670_, 0);
lean_dec(v_unused_2689_);
v___x_2672_ = v___x_2670_;
v_isShared_2673_ = v_isSharedCheck_2688_;
goto v_resetjp_2671_;
}
else
{
lean_dec(v___x_2670_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2688_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v_a_2667_);
lean_ctor_set(v___x_2674_, 1, v_a_2669_);
lean_inc_ref(v___x_2674_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set_tag(v___x_2672_, 1);
lean_ctor_set(v___x_2672_, 0, v___x_2674_);
v___x_2676_ = v___x_2672_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v___x_2677_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2607_, v_zetaDeltaFVarIds_2653_, v___x_2676_);
lean_dec_ref(v___x_2677_);
v___x_2678_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2607_, v_cache_2613_, v___x_2676_);
lean_dec_ref(v___x_2676_);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v___x_2678_, 0);
lean_dec(v_unused_2686_);
v___x_2680_ = v___x_2678_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_dec(v___x_2678_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2674_);
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2674_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
else
{
lean_object* v_a_2690_; 
lean_dec(v_a_2669_);
lean_dec(v_a_2667_);
v_a_2690_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2670_, 1);
v_a_2660_ = v_a_2690_;
goto v___jp_2659_;
}
}
else
{
lean_object* v_a_2691_; 
lean_dec(v_a_2667_);
lean_dec_ref_known(v___x_2649_, 7);
v_a_2691_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2668_, 1);
v_a_2660_ = v_a_2691_;
goto v___jp_2659_;
}
}
else
{
lean_object* v_a_2692_; 
lean_dec_ref_known(v___x_2649_, 7);
lean_dec_ref(v_value_2603_);
v_a_2692_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2666_, 1);
v_a_2660_ = v_a_2692_;
goto v___jp_2659_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* v_type_2698_, lean_object* v_value_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_2698_, v_value_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0(lean_object* v_00_u03b2_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0___redArg(){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0___redArg___boxed(lean_object* v___dummy_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0___redArg();
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0(lean_object* v_00_u03b2_2714_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
return v___x_2715_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_instMonadEIO___redArg();
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
lean_object* v___f_2749_; lean_object* v___f_2750_; lean_object* v___f_2751_; lean_object* v___f_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_12483__overap_2761_; lean_object* v___x_2762_; 
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
v___x_12483__overap_2761_ = lean_panic_fn_borrowed(v___x_2760_, v_msg_2719_);
lean_dec(v___x_2760_);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
v___x_2762_ = lean_apply_4(v___x_12483__overap_2761_, v___y_2720_, v___y_2721_, v___y_2722_, lean_box(0));
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
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v_nbuckets_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2827_ = lean_array_get_size(v_data_2826_);
v___x_2828_ = lean_unsigned_to_nat(2u);
v_nbuckets_2829_ = lean_nat_mul(v___x_2827_, v___x_2828_);
v___x_2830_ = lean_unsigned_to_nat(0u);
v___x_2831_ = lean_box(0);
v___x_2832_ = lean_mk_array(v_nbuckets_2829_, v___x_2831_);
v___x_2833_ = lean_array_propagate_mark(v_data_2826_, v___x_2832_);
v___x_2834_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v___x_2830_, v_data_2826_, v___x_2833_);
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
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v_nbuckets_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2992_ = lean_array_get_size(v_data_2991_);
v___x_2993_ = lean_unsigned_to_nat(2u);
v_nbuckets_2994_ = lean_nat_mul(v___x_2992_, v___x_2993_);
v___x_2995_ = lean_unsigned_to_nat(0u);
v___x_2996_ = lean_box(0);
v___x_2997_ = lean_mk_array(v_nbuckets_2994_, v___x_2996_);
v___x_2998_ = lean_array_propagate_mark(v_data_2991_, v___x_2997_);
v___x_2999_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v___x_2995_, v_data_2991_, v___x_2998_);
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
lean_dec_ref_known(v___x_3079_, 1);
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
lean_dec_ref_known(v___x_3106_, 1);
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
lean_dec_ref_known(v___x_3109_, 1);
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
lean_dec_ref_known(v_e_3060_, 4);
lean_dec_ref(v_g_3059_);
return v___x_3109_;
}
}
else
{
lean_dec_ref_known(v_e_3060_, 4);
lean_dec_ref(v_g_3059_);
return v___x_3106_;
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
lean_dec_ref_known(v___x_3115_, 1);
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
lean_dec_ref_known(v_e_3060_, 2);
lean_dec_ref(v_g_3059_);
return v___x_3115_;
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
lean_dec_ref_known(v___x_3090_, 1);
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
lean_dec_ref(v_e_3060_);
lean_dec_ref(v_g_3059_);
return v___x_3090_;
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
v___x_3071_ = lean_st_ref_put(v_a_3061_, v___x_3070_);
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
lean_dec_ref_known(v___y_3074_, 1);
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
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_Closure_mkValueTypeClosureAux_spec__0_spec__0___redArg___closed__0);
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
return v___x_3154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3156_ = lean_unsigned_to_nat(0u);
v___x_3157_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_3157_, 10, v___x_3155_);
return v___x_3157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2(void){
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3(void){
_start:
{
size_t v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3161_ = ((size_t)5ULL);
v___x_3162_ = lean_unsigned_to_nat(0u);
v___x_3163_ = lean_unsigned_to_nat(32u);
v___x_3164_ = lean_mk_empty_array_with_capacity(v___x_3163_);
v___x_3165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2);
v___x_3166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3164_);
lean_ctor_set(v___x_3166_, 2, v___x_3162_);
lean_ctor_set(v___x_3166_, 3, v___x_3162_);
lean_ctor_set_usize(v___x_3166_, 4, v___x_3161_);
return v___x_3166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3167_ = lean_box(1);
v___x_3168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3);
v___x_3169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
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
lean_object* v___x_3175_; lean_object* v_toCold_3176_; lean_object* v_env_3177_; lean_object* v_options_3178_; uint8_t v___x_3179_; lean_object* v_env_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3175_ = lean_st_ref_get(v___y_3173_);
v_toCold_3176_ = lean_ctor_get(v___y_3172_, 0);
v_env_3177_ = lean_ctor_get(v___x_3175_, 0);
lean_inc_ref(v_env_3177_);
lean_dec(v___x_3175_);
v_options_3178_ = lean_ctor_get(v_toCold_3176_, 2);
v___x_3179_ = 0;
v_env_3180_ = l_Lean_Environment_setRecordingDeps(v_env_3177_, v___x_3179_);
v___x_3181_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3182_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4);
lean_inc_ref(v_options_3178_);
v___x_3183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3183_, 0, v_env_3180_);
lean_ctor_set(v___x_3183_, 1, v___x_3181_);
lean_ctor_set(v___x_3183_, 2, v___x_3182_);
lean_ctor_set(v___x_3183_, 3, v_options_3178_);
v___x_3184_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v_msgData_3171_);
v___x_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___boxed(lean_object* v_msgData_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msgData_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(lean_object* v_msg_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v_ref_3195_; lean_object* v___x_3196_; lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3205_; 
v_ref_3195_ = lean_ctor_get(v___y_3192_, 2);
v___x_3196_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3191_, v___y_3192_, v___y_3193_);
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3205_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3205_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; lean_object* v___x_3203_; 
lean_inc(v_ref_3195_);
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_ref_3195_);
lean_ctor_set(v___x_3201_, 1, v_a_3197_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set_tag(v___x_3199_, 1);
lean_ctor_set(v___x_3199_, 0, v___x_3201_);
v___x_3203_ = v___x_3199_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg___boxed(lean_object* v_msg_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
return v_res_3210_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3211_; double v___x_3212_; 
v___x_3211_ = lean_unsigned_to_nat(0u);
v___x_3212_ = lean_float_of_nat(v___x_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object* v_cls_3216_, lean_object* v_msg_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_ref_3222_; lean_object* v___x_3223_; lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3270_; 
v_ref_3222_ = lean_ctor_get(v___y_3219_, 2);
v___x_3223_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3217_, v___y_3219_, v___y_3220_);
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3226_ = v___x_3223_;
v_isShared_3227_ = v_isSharedCheck_3270_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3270_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v_traceState_3229_; lean_object* v_env_3230_; lean_object* v_nextMacroScope_3231_; lean_object* v_ngen_3232_; lean_object* v_auxDeclNGen_3233_; lean_object* v_cache_3234_; lean_object* v_recordedDeps_3235_; lean_object* v_messages_3236_; lean_object* v_infoState_3237_; lean_object* v_snapshotTasks_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3269_; 
v___x_3228_ = lean_st_ref_take(v___y_3220_);
v_traceState_3229_ = lean_ctor_get(v___x_3228_, 4);
v_env_3230_ = lean_ctor_get(v___x_3228_, 0);
v_nextMacroScope_3231_ = lean_ctor_get(v___x_3228_, 1);
v_ngen_3232_ = lean_ctor_get(v___x_3228_, 2);
v_auxDeclNGen_3233_ = lean_ctor_get(v___x_3228_, 3);
v_cache_3234_ = lean_ctor_get(v___x_3228_, 5);
v_recordedDeps_3235_ = lean_ctor_get(v___x_3228_, 6);
v_messages_3236_ = lean_ctor_get(v___x_3228_, 7);
v_infoState_3237_ = lean_ctor_get(v___x_3228_, 8);
v_snapshotTasks_3238_ = lean_ctor_get(v___x_3228_, 9);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3240_ = v___x_3228_;
v_isShared_3241_ = v_isSharedCheck_3269_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_snapshotTasks_3238_);
lean_inc(v_infoState_3237_);
lean_inc(v_messages_3236_);
lean_inc(v_recordedDeps_3235_);
lean_inc(v_cache_3234_);
lean_inc(v_traceState_3229_);
lean_inc(v_auxDeclNGen_3233_);
lean_inc(v_ngen_3232_);
lean_inc(v_nextMacroScope_3231_);
lean_inc(v_env_3230_);
lean_dec(v___x_3228_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3269_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
uint64_t v_tid_3242_; lean_object* v_traces_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3268_; 
v_tid_3242_ = lean_ctor_get_uint64(v_traceState_3229_, sizeof(void*)*1);
v_traces_3243_ = lean_ctor_get(v_traceState_3229_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v_traceState_3229_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3245_ = v_traceState_3229_;
v_isShared_3246_ = v_isSharedCheck_3268_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_traces_3243_);
lean_dec(v_traceState_3229_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3268_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; double v___x_3249_; uint8_t v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3258_; 
v___x_3247_ = lean_box(0);
v___x_3248_ = lean_box(0);
v___x_3249_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3250_ = 0;
v___x_3251_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3252_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3252_, 0, v_cls_3216_);
lean_ctor_set(v___x_3252_, 1, v___x_3248_);
lean_ctor_set(v___x_3252_, 2, v___x_3251_);
lean_ctor_set_float(v___x_3252_, sizeof(void*)*3, v___x_3249_);
lean_ctor_set_float(v___x_3252_, sizeof(void*)*3 + 8, v___x_3249_);
lean_ctor_set_uint8(v___x_3252_, sizeof(void*)*3 + 16, v___x_3250_);
v___x_3253_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3254_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set(v___x_3254_, 1, v_a_3224_);
lean_ctor_set(v___x_3254_, 2, v___x_3253_);
lean_inc(v_ref_3222_);
v___x_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3255_, 0, v_ref_3222_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = l_Lean_PersistentArray_push___redArg(v_traces_3243_, v___x_3255_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3256_);
v___x_3258_ = v___x_3245_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3256_);
lean_ctor_set_uint64(v_reuseFailAlloc_3267_, sizeof(void*)*1, v_tid_3242_);
v___x_3258_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
lean_object* v___x_3260_; 
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 4, v___x_3258_);
v___x_3260_ = v___x_3240_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_env_3230_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_nextMacroScope_3231_);
lean_ctor_set(v_reuseFailAlloc_3266_, 2, v_ngen_3232_);
lean_ctor_set(v_reuseFailAlloc_3266_, 3, v_auxDeclNGen_3233_);
lean_ctor_set(v_reuseFailAlloc_3266_, 4, v___x_3258_);
lean_ctor_set(v_reuseFailAlloc_3266_, 5, v_cache_3234_);
lean_ctor_set(v_reuseFailAlloc_3266_, 6, v_recordedDeps_3235_);
lean_ctor_set(v_reuseFailAlloc_3266_, 7, v_messages_3236_);
lean_ctor_set(v_reuseFailAlloc_3266_, 8, v_infoState_3237_);
lean_ctor_set(v_reuseFailAlloc_3266_, 9, v_snapshotTasks_3238_);
v___x_3260_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3261_ = lean_st_ref_put(v___y_3220_, v___x_3260_);
v___x_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3247_);
lean_ctor_set(v___x_3262_, 1, v___y_3218_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3262_);
v___x_3264_ = v___x_3226_;
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
uint8_t v___x_17731__boxed_3318_; lean_object* v_res_3319_; 
v___x_17731__boxed_3318_ = lean_unbox(v___x_3311_);
v_res_3319_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(v___x_17731__boxed_3318_, v_m_3312_, v_e_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
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
v___x_3331_ = lean_unsigned_to_nat(390u);
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
lean_object* v_val_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3472_; 
v_val_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3472_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_val_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3472_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v_fst_3366_; lean_object* v_snd_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3471_; 
v_fst_3366_ = lean_ctor_get(v_val_3362_, 0);
v_snd_3367_ = lean_ctor_get(v_val_3362_, 1);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_val_3362_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3369_ = v_val_3362_;
v_isShared_3370_ = v_isSharedCheck_3471_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_snd_3367_);
lean_inc(v_fst_3366_);
lean_dec(v_val_3362_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3471_;
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
lean_object* v_toCold_3375_; lean_object* v_options_3376_; lean_object* v_inheritedTraceOptions_3377_; uint8_t v_hasTrace_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___f_3381_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3439_; lean_object* v_tempMark_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; 
lean_del_object(v___x_3369_);
lean_del_object(v___x_3364_);
v_toCold_3375_ = lean_ctor_get(v_a_3358_, 0);
v_options_3376_ = lean_ctor_get(v_toCold_3375_, 2);
v_inheritedTraceOptions_3377_ = lean_ctor_get(v_toCold_3375_, 11);
v_hasTrace_3378_ = lean_ctor_get_uint8(v_options_3376_, sizeof(void*)*1);
v___x_3379_ = 1;
v___x_3380_ = lean_box(v___x_3379_);
v___f_3381_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3381_, 0, v___x_3380_);
lean_closure_set(v___f_3381_, 1, v_m_3355_);
if (v_hasTrace_3378_ == 0)
{
lean_inc_ref(v_tempMark_3371_);
v___y_3439_ = v_a_3357_;
v_tempMark_3440_ = v_tempMark_3371_;
v___y_3441_ = v_a_3358_;
v___y_3442_ = v_a_3359_;
goto v___jp_3438_;
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
v___x_3448_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3449_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_3450_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3377_, v_options_3376_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_inc_ref(v_tempMark_3371_);
v___y_3439_ = v_a_3357_;
v_tempMark_3440_ = v_tempMark_3371_;
v___y_3441_ = v_a_3358_;
v___y_3442_ = v_a_3359_;
goto v___jp_3438_;
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3451_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15);
lean_inc(v___x_3373_);
v___x_3452_ = l_Lean_mkFVar(v___x_3373_);
v___x_3453_ = l_Lean_MessageData_ofExpr(v___x_3452_);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3451_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = l_Lean_LocalDecl_type(v_fst_3366_);
v___x_3458_ = l_Lean_MessageData_ofExpr(v___x_3457_);
v___x_3459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3456_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
v___x_3460_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v___x_3448_, v___x_3459_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v_snd_3462_; lean_object* v_tempMark_3463_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v_snd_3462_ = lean_ctor_get(v_a_3461_, 1);
lean_inc(v_snd_3462_);
lean_dec(v_a_3461_);
v_tempMark_3463_ = lean_ctor_get(v_snd_3462_, 0);
lean_inc_ref(v_tempMark_3463_);
v___y_3439_ = v_snd_3462_;
v_tempMark_3440_ = v_tempMark_3463_;
v___y_3441_ = v_a_3358_;
v___y_3442_ = v_a_3359_;
goto v___jp_3438_;
}
else
{
lean_dec_ref(v___f_3381_);
lean_dec(v___x_3373_);
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
return v___x_3460_;
}
}
}
v___jp_3382_:
{
uint8_t v___x_3386_; 
v___x_3386_ = l_Lean_LocalDecl_isLet(v_fst_3366_, v___x_3379_);
if (v___x_3386_ == 0)
{
lean_object* v_tempMark_3387_; lean_object* v_doneMark_3388_; lean_object* v_newDecls_3389_; lean_object* v_newArgs_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3435_; 
v_tempMark_3387_ = lean_ctor_get(v___y_3383_, 0);
v_doneMark_3388_ = lean_ctor_get(v___y_3383_, 1);
v_newDecls_3389_ = lean_ctor_get(v___y_3383_, 2);
v_newArgs_3390_ = lean_ctor_get(v___y_3383_, 3);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___y_3383_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3392_ = v___y_3383_;
v_isShared_3393_ = v_isSharedCheck_3435_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_newArgs_3390_);
lean_inc(v_newDecls_3389_);
lean_inc(v_doneMark_3388_);
lean_inc(v_tempMark_3387_);
lean_dec(v___y_3383_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3435_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3397_; 
v___x_3394_ = lean_box(0);
lean_inc(v___x_3373_);
v___x_3395_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_tempMark_3387_, v___x_3373_, v___x_3394_);
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v___x_3395_);
v___x_3397_ = v___x_3392_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3395_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_doneMark_3388_);
lean_ctor_set(v_reuseFailAlloc_3434_, 2, v_newDecls_3389_);
lean_ctor_set(v_reuseFailAlloc_3434_, 3, v_newArgs_3390_);
v___x_3397_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3398_ = l_Lean_LocalDecl_type(v_fst_3366_);
v___x_3399_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1);
v___x_3400_ = lean_st_mk_ref(v___x_3399_);
v___x_3401_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v___f_3381_, v___x_3398_, v___x_3400_, v___x_3397_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3433_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3404_ = v___x_3401_;
v_isShared_3405_ = v_isSharedCheck_3433_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3433_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v_snd_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3431_; 
v_snd_3406_ = lean_ctor_get(v_a_3402_, 1);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_a_3402_);
if (v_isSharedCheck_3431_ == 0)
{
lean_object* v_unused_3432_; 
v_unused_3432_ = lean_ctor_get(v_a_3402_, 0);
lean_dec(v_unused_3432_);
v___x_3408_ = v_a_3402_;
v_isShared_3409_ = v_isSharedCheck_3431_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_snd_3406_);
lean_dec(v_a_3402_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3431_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3410_; lean_object* v_tempMark_3411_; lean_object* v_doneMark_3412_; lean_object* v_newDecls_3413_; lean_object* v_newArgs_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3430_; 
v___x_3410_ = lean_st_ref_get(v___x_3400_);
lean_dec(v___x_3400_);
lean_dec(v___x_3410_);
v_tempMark_3411_ = lean_ctor_get(v_snd_3406_, 0);
v_doneMark_3412_ = lean_ctor_get(v_snd_3406_, 1);
v_newDecls_3413_ = lean_ctor_get(v_snd_3406_, 2);
v_newArgs_3414_ = lean_ctor_get(v_snd_3406_, 3);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_snd_3406_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3416_ = v_snd_3406_;
v_isShared_3417_ = v_isSharedCheck_3430_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_newArgs_3414_);
lean_inc(v_newDecls_3413_);
lean_inc(v_doneMark_3412_);
lean_inc(v_tempMark_3411_);
lean_dec(v_snd_3406_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3430_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3418_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_doneMark_3412_, v___x_3373_, v___x_3394_);
v___x_3419_ = lean_array_push(v_newDecls_3413_, v_fst_3366_);
v___x_3420_ = lean_array_push(v_newArgs_3414_, v_snd_3367_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 3, v___x_3420_);
lean_ctor_set(v___x_3416_, 2, v___x_3419_);
lean_ctor_set(v___x_3416_, 1, v___x_3418_);
v___x_3422_ = v___x_3416_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_tempMark_3411_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3429_, 2, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3429_, 3, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3424_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 1, v___x_3422_);
lean_ctor_set(v___x_3408_, 0, v___x_3394_);
v___x_3424_ = v___x_3408_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3394_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3426_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v___x_3424_);
v___x_3426_ = v___x_3404_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3400_);
lean_dec(v___x_3373_);
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
return v___x_3401_;
}
}
}
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
lean_dec_ref(v___f_3381_);
lean_dec(v___x_3373_);
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
v___x_3436_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5);
v___x_3437_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v___x_3436_, v___y_3383_, v___y_3384_, v___y_3385_);
return v___x_3437_;
}
}
v___jp_3438_:
{
uint8_t v___x_3443_; 
v___x_3443_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_tempMark_3440_, v___x_3373_);
lean_dec_ref(v_tempMark_3440_);
if (v___x_3443_ == 0)
{
v___y_3383_ = v___y_3439_;
v___y_3384_ = v___y_3441_;
v___y_3385_ = v___y_3442_;
goto v___jp_3382_;
}
else
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_dec_ref(v___y_3439_);
v___x_3444_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7);
v___x_3445_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v___x_3444_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v_snd_3447_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v___x_3445_, 1);
v_snd_3447_ = lean_ctor_get(v_a_3446_, 1);
lean_inc(v_snd_3447_);
lean_dec(v_a_3446_);
v___y_3383_ = v_snd_3447_;
v___y_3384_ = v___y_3441_;
v___y_3385_ = v___y_3442_;
goto v___jp_3382_;
}
else
{
lean_dec_ref(v___f_3381_);
lean_dec(v___x_3373_);
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
return v___x_3445_;
}
}
}
}
else
{
lean_object* v___x_3464_; lean_object* v___x_3466_; 
lean_dec(v___x_3373_);
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
lean_dec_ref(v_m_3355_);
v___x_3464_ = lean_box(0);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 1, v_a_3357_);
lean_ctor_set(v___x_3369_, 0, v___x_3464_);
v___x_3466_ = v___x_3369_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3464_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_a_3357_);
v___x_3466_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3468_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set_tag(v___x_3364_, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3466_);
v___x_3468_ = v___x_3364_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3466_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
}
}
else
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_dec(v___x_3361_);
lean_dec_ref(v_m_3355_);
v___x_3473_ = lean_box(0);
v___x_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v_a_3357_);
v___x_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
return v___x_3475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t v___x_3476_, lean_object* v_m_3477_, lean_object* v_e_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v___y_3484_; uint8_t v___x_3488_; 
v___x_3488_ = l_Lean_Expr_hasFVar(v_e_3478_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
lean_dec_ref(v_m_3477_);
v___x_3489_ = lean_box(v___x_3488_);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v___y_3479_);
v___x_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
return v___x_3491_;
}
else
{
uint8_t v___x_3492_; 
v___x_3492_ = l_Lean_Expr_isFVar(v_e_3478_);
if (v___x_3492_ == 0)
{
lean_dec_ref(v_m_3477_);
v___y_3484_ = v___y_3479_;
goto v___jp_3483_;
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = l_Lean_Expr_fvarId_x21(v_e_3478_);
v___x_3494_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3477_, v___x_3493_, v___y_3479_, v___y_3480_, v___y_3481_);
lean_dec(v___x_3493_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v_snd_3496_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
v_snd_3496_ = lean_ctor_get(v_a_3495_, 1);
lean_inc(v_snd_3496_);
lean_dec(v_a_3495_);
v___y_3484_ = v_snd_3496_;
goto v___jp_3483_;
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
v_a_3497_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3494_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3494_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
}
v___jp_3483_:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3485_ = lean_box(v___x_3476_);
v___x_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set(v___x_3486_, 1, v___y_3484_);
v___x_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
return v___x_3487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object* v_m_3505_, lean_object* v_fvarId_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3505_, v_fvarId_3506_, v_a_3507_, v_a_3508_, v_a_3509_);
lean_dec(v_a_3509_);
lean_dec_ref(v_a_3508_);
lean_dec(v_fvarId_3506_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object* v_00_u03b2_3512_, lean_object* v_m_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3513_, v_a_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object* v_00_u03b2_3516_, lean_object* v_m_3517_, lean_object* v_a_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(v_00_u03b2_3516_, v_m_3517_, v_a_3518_);
lean_dec(v_a_3518_);
lean_dec_ref(v_m_3517_);
return v_res_3519_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object* v_00_u03b2_3520_, lean_object* v_m_3521_, lean_object* v_a_3522_){
_start:
{
uint8_t v___x_3523_; 
v___x_3523_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_3521_, v_a_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object* v_00_u03b2_3524_, lean_object* v_m_3525_, lean_object* v_a_3526_){
_start:
{
uint8_t v_res_3527_; lean_object* v_r_3528_; 
v_res_3527_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(v_00_u03b2_3524_, v_m_3525_, v_a_3526_);
lean_dec(v_a_3526_);
lean_dec_ref(v_m_3525_);
v_r_3528_ = lean_box(v_res_3527_);
return v_r_3528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object* v_00_u03b2_3529_, lean_object* v_m_3530_, lean_object* v_a_3531_, lean_object* v_b_3532_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_m_3530_, v_a_3531_, v_b_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object* v_00_u03b1_3534_, lean_object* v_msg_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3535_, v___y_3537_, v___y_3538_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object* v_00_u03b1_3541_, lean_object* v_msg_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v_00_u03b1_3541_, v_msg_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec_ref(v___y_3543_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object* v_00_u03b2_3548_, lean_object* v_a_3549_, lean_object* v_x_3550_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3549_, v_x_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3552_, lean_object* v_a_3553_, lean_object* v_x_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(v_00_u03b2_3552_, v_a_3553_, v_x_3554_);
lean_dec(v_x_3554_);
lean_dec(v_a_3553_);
return v_res_3555_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_object* v_00_u03b2_3556_, lean_object* v_a_3557_, lean_object* v_x_3558_){
_start:
{
uint8_t v___x_3559_; 
v___x_3559_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3557_, v_x_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3560_, lean_object* v_a_3561_, lean_object* v_x_3562_){
_start:
{
uint8_t v_res_3563_; lean_object* v_r_3564_; 
v_res_3563_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(v_00_u03b2_3560_, v_a_3561_, v_x_3562_);
lean_dec(v_x_3562_);
lean_dec(v_a_3561_);
v_r_3564_ = lean_box(v_res_3563_);
return v_r_3564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(lean_object* v_00_u03b2_3565_, lean_object* v_data_3566_){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_data_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(lean_object* v_00_u03b2_3568_, lean_object* v_m_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_3569_, v_a_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3572_, lean_object* v_m_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(v_00_u03b2_3572_, v_m_3573_, v_a_3574_);
lean_dec_ref(v_a_3574_);
lean_dec_ref(v_m_3573_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(lean_object* v_00_u03b2_3576_, lean_object* v_m_3577_, lean_object* v_a_3578_, lean_object* v_b_3579_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_3577_, v_a_3578_, v_b_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_3581_, lean_object* v_i_3582_, lean_object* v_source_3583_, lean_object* v_target_3584_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v_i_3582_, v_source_3583_, v_target_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_3586_, lean_object* v_a_3587_, lean_object* v_x_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_3587_, v_x_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3590_, lean_object* v_a_3591_, lean_object* v_x_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(v_00_u03b2_3590_, v_a_3591_, v_x_3592_);
lean_dec(v_x_3592_);
lean_dec_ref(v_a_3591_);
return v_res_3593_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3594_, lean_object* v_a_3595_, lean_object* v_x_3596_){
_start:
{
uint8_t v___x_3597_; 
v___x_3597_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3595_, v_x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3598_, lean_object* v_a_3599_, lean_object* v_x_3600_){
_start:
{
uint8_t v_res_3601_; lean_object* v_r_3602_; 
v_res_3601_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(v_00_u03b2_3598_, v_a_3599_, v_x_3600_);
lean_dec(v_x_3600_);
lean_dec_ref(v_a_3599_);
v_r_3602_ = lean_box(v_res_3601_);
return v_r_3602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b2_3603_, lean_object* v_data_3604_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_data_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13(lean_object* v_00_u03b2_3606_, lean_object* v_a_3607_, lean_object* v_b_3608_, lean_object* v_x_3609_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3607_, v_b_3608_, v_x_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_3611_, lean_object* v_x_3612_, lean_object* v_x_3613_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_x_3612_, v_x_3613_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17(lean_object* v_00_u03b2_3615_, lean_object* v_i_3616_, lean_object* v_source_3617_, lean_object* v_target_3618_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v_i_3616_, v_source_3617_, v_target_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18(lean_object* v_00_u03b2_3620_, lean_object* v_x_3621_, lean_object* v_x_3622_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_x_3621_, v_x_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object* v_msg_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v___f_3629_; lean_object* v___x_7408__overap_3630_; lean_object* v___x_3631_; 
v___f_3629_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___closed__0));
v___x_7408__overap_3630_ = lean_panic_fn_borrowed(v___f_3629_, v_msg_3625_);
lean_inc(v___y_3627_);
lean_inc_ref(v___y_3626_);
v___x_3631_ = lean_apply_3(v___x_7408__overap_3630_, v___y_3626_, v___y_3627_, lean_box(0));
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___boxed(lean_object* v_msg_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v_msg_3632_, v___y_3633_, v___y_3634_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object* v_newDecls_3637_, lean_object* v_newArgs_3638_, lean_object* v_____r_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3644_, 0, v_newDecls_3637_);
lean_ctor_set(v___x_3644_, 1, v_newArgs_3638_);
v___x_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
lean_ctor_set(v___x_3645_, 1, v___y_3640_);
v___x_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object* v_newDecls_3647_, lean_object* v_newArgs_3648_, lean_object* v_____r_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3647_, v_newArgs_3648_, v_____r_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(lean_object* v_cls_3655_, lean_object* v_msg_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v_ref_3660_; lean_object* v___x_3661_; lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3707_; 
v_ref_3660_ = lean_ctor_get(v___y_3657_, 2);
v___x_3661_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3656_, v___y_3657_, v___y_3658_);
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3664_ = v___x_3661_;
v_isShared_3665_ = v_isSharedCheck_3707_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3661_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3707_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; lean_object* v_traceState_3667_; lean_object* v_env_3668_; lean_object* v_nextMacroScope_3669_; lean_object* v_ngen_3670_; lean_object* v_auxDeclNGen_3671_; lean_object* v_cache_3672_; lean_object* v_recordedDeps_3673_; lean_object* v_messages_3674_; lean_object* v_infoState_3675_; lean_object* v_snapshotTasks_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3706_; 
v___x_3666_ = lean_st_ref_take(v___y_3658_);
v_traceState_3667_ = lean_ctor_get(v___x_3666_, 4);
v_env_3668_ = lean_ctor_get(v___x_3666_, 0);
v_nextMacroScope_3669_ = lean_ctor_get(v___x_3666_, 1);
v_ngen_3670_ = lean_ctor_get(v___x_3666_, 2);
v_auxDeclNGen_3671_ = lean_ctor_get(v___x_3666_, 3);
v_cache_3672_ = lean_ctor_get(v___x_3666_, 5);
v_recordedDeps_3673_ = lean_ctor_get(v___x_3666_, 6);
v_messages_3674_ = lean_ctor_get(v___x_3666_, 7);
v_infoState_3675_ = lean_ctor_get(v___x_3666_, 8);
v_snapshotTasks_3676_ = lean_ctor_get(v___x_3666_, 9);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3678_ = v___x_3666_;
v_isShared_3679_ = v_isSharedCheck_3706_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_snapshotTasks_3676_);
lean_inc(v_infoState_3675_);
lean_inc(v_messages_3674_);
lean_inc(v_recordedDeps_3673_);
lean_inc(v_cache_3672_);
lean_inc(v_traceState_3667_);
lean_inc(v_auxDeclNGen_3671_);
lean_inc(v_ngen_3670_);
lean_inc(v_nextMacroScope_3669_);
lean_inc(v_env_3668_);
lean_dec(v___x_3666_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3706_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
uint64_t v_tid_3680_; lean_object* v_traces_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3705_; 
v_tid_3680_ = lean_ctor_get_uint64(v_traceState_3667_, sizeof(void*)*1);
v_traces_3681_ = lean_ctor_get(v_traceState_3667_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_traceState_3667_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3683_ = v_traceState_3667_;
v_isShared_3684_ = v_isSharedCheck_3705_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_traces_3681_);
lean_dec(v_traceState_3667_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3705_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; double v___x_3687_; uint8_t v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3696_; 
v___x_3685_ = lean_box(0);
v___x_3686_ = lean_box(0);
v___x_3687_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3688_ = 0;
v___x_3689_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3690_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3690_, 0, v_cls_3655_);
lean_ctor_set(v___x_3690_, 1, v___x_3686_);
lean_ctor_set(v___x_3690_, 2, v___x_3689_);
lean_ctor_set_float(v___x_3690_, sizeof(void*)*3, v___x_3687_);
lean_ctor_set_float(v___x_3690_, sizeof(void*)*3 + 8, v___x_3687_);
lean_ctor_set_uint8(v___x_3690_, sizeof(void*)*3 + 16, v___x_3688_);
v___x_3691_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3692_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v_a_3662_);
lean_ctor_set(v___x_3692_, 2, v___x_3691_);
lean_inc(v_ref_3660_);
v___x_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3693_, 0, v_ref_3660_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
v___x_3694_ = l_Lean_PersistentArray_push___redArg(v_traces_3681_, v___x_3693_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v___x_3694_);
v___x_3696_ = v___x_3683_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3694_);
lean_ctor_set_uint64(v_reuseFailAlloc_3704_, sizeof(void*)*1, v_tid_3680_);
v___x_3696_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3698_; 
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 4, v___x_3696_);
v___x_3698_ = v___x_3678_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_env_3668_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_nextMacroScope_3669_);
lean_ctor_set(v_reuseFailAlloc_3703_, 2, v_ngen_3670_);
lean_ctor_set(v_reuseFailAlloc_3703_, 3, v_auxDeclNGen_3671_);
lean_ctor_set(v_reuseFailAlloc_3703_, 4, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3703_, 5, v_cache_3672_);
lean_ctor_set(v_reuseFailAlloc_3703_, 6, v_recordedDeps_3673_);
lean_ctor_set(v_reuseFailAlloc_3703_, 7, v_messages_3674_);
lean_ctor_set(v_reuseFailAlloc_3703_, 8, v_infoState_3675_);
lean_ctor_set(v_reuseFailAlloc_3703_, 9, v_snapshotTasks_3676_);
v___x_3698_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3699_; lean_object* v___x_3701_; 
v___x_3699_ = lean_st_ref_put(v___y_3658_, v___x_3698_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3685_);
v___x_3701_ = v___x_3664_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3685_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(lean_object* v_cls_3708_, lean_object* v_msg_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3708_, v_msg_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(size_t v_sz_3714_, size_t v_i_3715_, lean_object* v_bs_3716_){
_start:
{
uint8_t v___x_3717_; 
v___x_3717_ = lean_usize_dec_lt(v_i_3715_, v_sz_3714_);
if (v___x_3717_ == 0)
{
return v_bs_3716_;
}
else
{
lean_object* v_v_3718_; lean_object* v___x_3719_; lean_object* v_bs_x27_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; size_t v___x_3723_; size_t v___x_3724_; lean_object* v___x_3725_; 
v_v_3718_ = lean_array_uget(v_bs_3716_, v_i_3715_);
v___x_3719_ = lean_unsigned_to_nat(0u);
v_bs_x27_3720_ = lean_array_uset(v_bs_3716_, v_i_3715_, v___x_3719_);
v___x_3721_ = l_Lean_LocalDecl_fvarId(v_v_3718_);
lean_dec(v_v_3718_);
v___x_3722_ = l_Lean_mkFVar(v___x_3721_);
v___x_3723_ = ((size_t)1ULL);
v___x_3724_ = lean_usize_add(v_i_3715_, v___x_3723_);
v___x_3725_ = lean_array_uset(v_bs_x27_3720_, v_i_3715_, v___x_3722_);
v_i_3715_ = v___x_3724_;
v_bs_3716_ = v___x_3725_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(lean_object* v_sz_3727_, lean_object* v_i_3728_, lean_object* v_bs_3729_){
_start:
{
size_t v_sz_boxed_3730_; size_t v_i_boxed_3731_; lean_object* v_res_3732_; 
v_sz_boxed_3730_ = lean_unbox_usize(v_sz_3727_);
lean_dec(v_sz_3727_);
v_i_boxed_3731_ = lean_unbox_usize(v_i_3728_);
lean_dec(v_i_3728_);
v_res_3732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_boxed_3730_, v_i_boxed_3731_, v_bs_3729_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(lean_object* v___x_3733_, lean_object* v_as_3734_, size_t v_sz_3735_, size_t v_i_3736_, lean_object* v_b_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
uint8_t v___x_3742_; 
v___x_3742_ = lean_usize_dec_lt(v_i_3736_, v_sz_3735_);
if (v___x_3742_ == 0)
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
lean_dec_ref(v___x_3733_);
v___x_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3743_, 0, v_b_3737_);
lean_ctor_set(v___x_3743_, 1, v___y_3738_);
v___x_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
return v___x_3744_;
}
else
{
lean_object* v___x_3745_; lean_object* v_a_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3745_ = lean_box(0);
v_a_3746_ = lean_array_uget_borrowed(v_as_3734_, v_i_3736_);
v___x_3747_ = l_Lean_LocalDecl_fvarId(v_a_3746_);
lean_inc_ref(v___x_3733_);
v___x_3748_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v___x_3733_, v___x_3747_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___x_3747_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; lean_object* v_snd_3750_; size_t v___x_3751_; size_t v___x_3752_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref_known(v___x_3748_, 1);
v_snd_3750_ = lean_ctor_get(v_a_3749_, 1);
lean_inc(v_snd_3750_);
lean_dec(v_a_3749_);
v___x_3751_ = ((size_t)1ULL);
v___x_3752_ = lean_usize_add(v_i_3736_, v___x_3751_);
v_i_3736_ = v___x_3752_;
v_b_3737_ = v___x_3745_;
v___y_3738_ = v_snd_3750_;
goto _start;
}
else
{
lean_dec_ref(v___x_3733_);
return v___x_3748_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object* v___x_3754_, lean_object* v_as_3755_, lean_object* v_sz_3756_, lean_object* v_i_3757_, lean_object* v_b_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
size_t v_sz_boxed_3763_; size_t v_i_boxed_3764_; lean_object* v_res_3765_; 
v_sz_boxed_3763_ = lean_unbox_usize(v_sz_3756_);
lean_dec(v_sz_3756_);
v_i_boxed_3764_ = lean_unbox_usize(v_i_3757_);
lean_dec(v_i_3757_);
v_res_3765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v___x_3754_, v_as_3755_, v_sz_boxed_3763_, v_i_boxed_3764_, v_b_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec_ref(v_as_3755_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
if (lean_obj_tag(v_a_3766_) == 0)
{
lean_object* v___x_3768_; 
v___x_3768_ = l_List_reverse___redArg(v_a_3767_);
return v___x_3768_;
}
else
{
lean_object* v_head_3769_; lean_object* v_tail_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3779_; 
v_head_3769_ = lean_ctor_get(v_a_3766_, 0);
v_tail_3770_ = lean_ctor_get(v_a_3766_, 1);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_a_3766_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3772_ = v_a_3766_;
v_isShared_3773_ = v_isSharedCheck_3779_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_tail_3770_);
lean_inc(v_head_3769_);
lean_dec(v_a_3766_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3779_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
v___x_3774_ = l_Lean_MessageData_ofExpr(v_head_3769_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 1, v_a_3767_);
lean_ctor_set(v___x_3772_, 0, v___x_3774_);
v___x_3776_ = v___x_3772_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_a_3767_);
v___x_3776_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
v_a_3766_ = v_tail_3770_;
v_a_3767_ = v___x_3776_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(lean_object* v_a_3780_, lean_object* v_b_3781_, lean_object* v_x_3782_){
_start:
{
if (lean_obj_tag(v_x_3782_) == 0)
{
lean_dec(v_b_3781_);
lean_dec(v_a_3780_);
return v_x_3782_;
}
else
{
lean_object* v_key_3783_; lean_object* v_value_3784_; lean_object* v_tail_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3797_; 
v_key_3783_ = lean_ctor_get(v_x_3782_, 0);
v_value_3784_ = lean_ctor_get(v_x_3782_, 1);
v_tail_3785_ = lean_ctor_get(v_x_3782_, 2);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_x_3782_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3787_ = v_x_3782_;
v_isShared_3788_ = v_isSharedCheck_3797_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_tail_3785_);
lean_inc(v_value_3784_);
lean_inc(v_key_3783_);
lean_dec(v_x_3782_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3797_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
uint8_t v___x_3789_; 
v___x_3789_ = l_Lean_instBEqFVarId_beq(v_key_3783_, v_a_3780_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; lean_object* v___x_3792_; 
v___x_3790_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_3780_, v_b_3781_, v_tail_3785_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 2, v___x_3790_);
v___x_3792_ = v___x_3787_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_key_3783_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_value_3784_);
lean_ctor_set(v_reuseFailAlloc_3793_, 2, v___x_3790_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
else
{
lean_object* v___x_3795_; 
lean_dec(v_value_3784_);
lean_dec(v_key_3783_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 1, v_b_3781_);
lean_ctor_set(v___x_3787_, 0, v_a_3780_);
v___x_3795_ = v___x_3787_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3780_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_b_3781_);
lean_ctor_set(v_reuseFailAlloc_3796_, 2, v_tail_3785_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(lean_object* v_m_3798_, lean_object* v_a_3799_, lean_object* v_b_3800_){
_start:
{
lean_object* v_size_3801_; lean_object* v_buckets_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3845_; 
v_size_3801_ = lean_ctor_get(v_m_3798_, 0);
v_buckets_3802_ = lean_ctor_get(v_m_3798_, 1);
v_isSharedCheck_3845_ = !lean_is_exclusive(v_m_3798_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3804_ = v_m_3798_;
v_isShared_3805_ = v_isSharedCheck_3845_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_buckets_3802_);
lean_inc(v_size_3801_);
lean_dec(v_m_3798_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3845_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3806_; uint64_t v___x_3807_; uint64_t v___x_3808_; uint64_t v___x_3809_; uint64_t v_fold_3810_; uint64_t v___x_3811_; uint64_t v___x_3812_; uint64_t v___x_3813_; size_t v___x_3814_; size_t v___x_3815_; size_t v___x_3816_; size_t v___x_3817_; size_t v___x_3818_; lean_object* v_bkt_3819_; uint8_t v___x_3820_; 
v___x_3806_ = lean_array_get_size(v_buckets_3802_);
v___x_3807_ = l_Lean_instHashableFVarId_hash(v_a_3799_);
v___x_3808_ = 32ULL;
v___x_3809_ = lean_uint64_shift_right(v___x_3807_, v___x_3808_);
v_fold_3810_ = lean_uint64_xor(v___x_3807_, v___x_3809_);
v___x_3811_ = 16ULL;
v___x_3812_ = lean_uint64_shift_right(v_fold_3810_, v___x_3811_);
v___x_3813_ = lean_uint64_xor(v_fold_3810_, v___x_3812_);
v___x_3814_ = lean_uint64_to_usize(v___x_3813_);
v___x_3815_ = lean_usize_of_nat(v___x_3806_);
v___x_3816_ = ((size_t)1ULL);
v___x_3817_ = lean_usize_sub(v___x_3815_, v___x_3816_);
v___x_3818_ = lean_usize_land(v___x_3814_, v___x_3817_);
v_bkt_3819_ = lean_array_uget_borrowed(v_buckets_3802_, v___x_3818_);
v___x_3820_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3799_, v_bkt_3819_);
if (v___x_3820_ == 0)
{
lean_object* v___x_3821_; lean_object* v_size_x27_3822_; lean_object* v___x_3823_; lean_object* v_buckets_x27_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; 
v___x_3821_ = lean_unsigned_to_nat(1u);
v_size_x27_3822_ = lean_nat_add(v_size_3801_, v___x_3821_);
lean_dec(v_size_3801_);
lean_inc(v_bkt_3819_);
v___x_3823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3823_, 0, v_a_3799_);
lean_ctor_set(v___x_3823_, 1, v_b_3800_);
lean_ctor_set(v___x_3823_, 2, v_bkt_3819_);
v_buckets_x27_3824_ = lean_array_uset(v_buckets_3802_, v___x_3818_, v___x_3823_);
v___x_3825_ = lean_unsigned_to_nat(4u);
v___x_3826_ = lean_nat_mul(v_size_x27_3822_, v___x_3825_);
v___x_3827_ = lean_unsigned_to_nat(3u);
v___x_3828_ = lean_nat_div(v___x_3826_, v___x_3827_);
lean_dec(v___x_3826_);
v___x_3829_ = lean_array_get_size(v_buckets_x27_3824_);
v___x_3830_ = lean_nat_dec_le(v___x_3828_, v___x_3829_);
lean_dec(v___x_3828_);
if (v___x_3830_ == 0)
{
lean_object* v_val_3831_; lean_object* v___x_3833_; 
v_val_3831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_3824_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 1, v_val_3831_);
lean_ctor_set(v___x_3804_, 0, v_size_x27_3822_);
v___x_3833_ = v___x_3804_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_size_x27_3822_);
lean_ctor_set(v_reuseFailAlloc_3834_, 1, v_val_3831_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
else
{
lean_object* v___x_3836_; 
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 1, v_buckets_x27_3824_);
lean_ctor_set(v___x_3804_, 0, v_size_x27_3822_);
v___x_3836_ = v___x_3804_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_size_x27_3822_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v_buckets_x27_3824_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
else
{
lean_object* v___x_3838_; lean_object* v_buckets_x27_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3843_; 
lean_inc(v_bkt_3819_);
v___x_3838_ = lean_box(0);
v_buckets_x27_3839_ = lean_array_uset(v_buckets_3802_, v___x_3818_, v___x_3838_);
v___x_3840_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_3799_, v_b_3800_, v_bkt_3819_);
v___x_3841_ = lean_array_uset(v_buckets_x27_3839_, v___x_3818_, v___x_3840_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 1, v___x_3841_);
v___x_3843_ = v___x_3804_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_size_3801_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v___x_3841_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(lean_object* v_as_3846_, size_t v_sz_3847_, size_t v_i_3848_, lean_object* v_b_3849_){
_start:
{
uint8_t v___x_3851_; 
v___x_3851_ = lean_usize_dec_lt(v_i_3848_, v_sz_3847_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3852_, 0, v_b_3849_);
return v___x_3852_;
}
else
{
lean_object* v_snd_3853_; lean_object* v_fst_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3889_; 
v_snd_3853_ = lean_ctor_get(v_b_3849_, 1);
v_fst_3854_ = lean_ctor_get(v_b_3849_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_b_3849_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3856_ = v_b_3849_;
v_isShared_3857_ = v_isSharedCheck_3889_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_snd_3853_);
lean_inc(v_fst_3854_);
lean_dec(v_b_3849_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3889_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v_array_3858_; lean_object* v_start_3859_; lean_object* v_stop_3860_; uint8_t v___x_3861_; 
v_array_3858_ = lean_ctor_get(v_snd_3853_, 0);
v_start_3859_ = lean_ctor_get(v_snd_3853_, 1);
v_stop_3860_ = lean_ctor_get(v_snd_3853_, 2);
v___x_3861_ = lean_nat_dec_lt(v_start_3859_, v_stop_3860_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3863_; 
if (v_isShared_3857_ == 0)
{
v___x_3863_ = v___x_3856_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_fst_3854_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_snd_3853_);
v___x_3863_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; 
v___x_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
return v___x_3864_;
}
}
else
{
lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3885_; 
lean_inc(v_stop_3860_);
lean_inc(v_start_3859_);
lean_inc_ref(v_array_3858_);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_snd_3853_);
if (v_isSharedCheck_3885_ == 0)
{
lean_object* v_unused_3886_; lean_object* v_unused_3887_; lean_object* v_unused_3888_; 
v_unused_3886_ = lean_ctor_get(v_snd_3853_, 2);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_snd_3853_, 1);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_snd_3853_, 0);
lean_dec(v_unused_3888_);
v___x_3867_ = v_snd_3853_;
v_isShared_3868_ = v_isSharedCheck_3885_;
goto v_resetjp_3866_;
}
else
{
lean_dec(v_snd_3853_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3885_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v_a_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3874_; 
v_a_3869_ = lean_array_uget_borrowed(v_as_3846_, v_i_3848_);
v___x_3870_ = lean_array_fget(v_array_3858_, v_start_3859_);
v___x_3871_ = lean_unsigned_to_nat(1u);
v___x_3872_ = lean_nat_add(v_start_3859_, v___x_3871_);
lean_dec(v_start_3859_);
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 1, v___x_3872_);
v___x_3874_ = v___x_3867_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_array_3858_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v___x_3872_);
lean_ctor_set(v_reuseFailAlloc_3884_, 2, v_stop_3860_);
v___x_3874_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v___x_3875_; lean_object* v___x_3877_; 
v___x_3875_ = l_Lean_LocalDecl_fvarId(v_a_3869_);
lean_inc(v_a_3869_);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 1, v___x_3870_);
lean_ctor_set(v___x_3856_, 0, v_a_3869_);
v___x_3877_ = v___x_3856_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3869_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v___x_3870_);
v___x_3877_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; size_t v___x_3880_; size_t v___x_3881_; 
v___x_3878_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(v_fst_3854_, v___x_3875_, v___x_3877_);
v___x_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
lean_ctor_set(v___x_3879_, 1, v___x_3874_);
v___x_3880_ = ((size_t)1ULL);
v___x_3881_ = lean_usize_add(v_i_3848_, v___x_3880_);
v_i_3848_ = v___x_3881_;
v_b_3849_ = v___x_3879_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg___boxed(lean_object* v_as_3890_, lean_object* v_sz_3891_, lean_object* v_i_3892_, lean_object* v_b_3893_, lean_object* v___y_3894_){
_start:
{
size_t v_sz_boxed_3895_; size_t v_i_boxed_3896_; lean_object* v_res_3897_; 
v_sz_boxed_3895_ = lean_unbox_usize(v_sz_3891_);
lean_dec(v_sz_3891_);
v_i_boxed_3896_ = lean_unbox_usize(v_i_3892_);
lean_dec(v_i_3892_);
v_res_3897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_3890_, v_sz_boxed_3895_, v_i_boxed_3896_, v_b_3893_);
lean_dec_ref(v_as_3890_);
return v_res_3897_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2(void){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3900_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1));
v___x_3901_ = lean_unsigned_to_nat(2u);
v___x_3902_ = lean_unsigned_to_nat(372u);
v___x_3903_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3904_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3905_ = l_mkPanicMessageWithDecl(v___x_3904_, v___x_3903_, v___x_3902_, v___x_3901_, v___x_3900_);
return v___x_3905_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3));
v___x_3908_ = lean_unsigned_to_nat(2u);
v___x_3909_ = lean_unsigned_to_nat(373u);
v___x_3910_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3911_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3912_ = l_mkPanicMessageWithDecl(v___x_3911_, v___x_3910_, v___x_3909_, v___x_3908_, v___x_3907_);
return v___x_3912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5(void){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3913_ = lean_box(0);
v___x_3914_ = lean_unsigned_to_nat(16u);
v___x_3915_ = lean_mk_array(v___x_3914_, v___x_3913_);
return v___x_3915_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6(void){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5);
v___x_3917_ = lean_unsigned_to_nat(0u);
v___x_3918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
lean_ctor_set(v___x_3918_, 1, v___x_3916_);
return v___x_3918_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7));
v___x_3921_ = l_Lean_stringToMessageData(v___x_3920_);
return v___x_3921_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10(void){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9));
v___x_3924_ = l_Lean_stringToMessageData(v___x_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object* v_sortedDecls_3925_, lean_object* v_sortedArgs_3926_, lean_object* v_toSortDecls_3927_, lean_object* v_toSortArgs_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_){
_start:
{
lean_object* v___y_3933_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v_snd_3956_; lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v___x_3958_ = lean_array_get_size(v_sortedDecls_3925_);
v___x_3959_ = lean_array_get_size(v_sortedArgs_3926_);
v___x_3960_ = lean_nat_dec_eq(v___x_3958_, v___x_3959_);
if (v___x_3960_ == 0)
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
lean_dec_ref(v_toSortArgs_3928_);
lean_dec_ref(v_sortedArgs_3926_);
lean_dec_ref(v_sortedDecls_3925_);
v___x_3961_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2);
v___x_3962_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v___x_3961_, v_a_3929_, v_a_3930_);
return v___x_3962_;
}
else
{
lean_object* v___x_3963_; lean_object* v___x_3964_; uint8_t v___x_3965_; 
v___x_3963_ = lean_array_get_size(v_toSortDecls_3927_);
v___x_3964_ = lean_array_get_size(v_toSortArgs_3928_);
v___x_3965_ = lean_nat_dec_eq(v___x_3963_, v___x_3964_);
if (v___x_3965_ == 0)
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
lean_dec_ref(v_toSortArgs_3928_);
lean_dec_ref(v_sortedArgs_3926_);
lean_dec_ref(v_sortedDecls_3925_);
v___x_3966_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4);
v___x_3967_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v___x_3966_, v_a_3929_, v_a_3930_);
return v___x_3967_;
}
else
{
lean_object* v___x_3968_; uint8_t v___x_3969_; 
v___x_3968_ = lean_unsigned_to_nat(0u);
v___x_3969_ = lean_nat_dec_eq(v___x_3963_, v___x_3968_);
if (v___x_3969_ == 0)
{
lean_object* v_toCold_3970_; lean_object* v_options_3971_; lean_object* v_inheritedTraceOptions_3972_; uint8_t v_hasTrace_3973_; lean_object* v___x_3974_; lean_object* v_cls_3975_; lean_object* v___y_3977_; lean_object* v___y_3978_; 
v_toCold_3970_ = lean_ctor_get(v_a_3929_, 0);
v_options_3971_ = lean_ctor_get(v_toCold_3970_, 2);
v_inheritedTraceOptions_3972_ = lean_ctor_get(v_toCold_3970_, 11);
v_hasTrace_3973_ = lean_ctor_get_uint8(v_options_3971_, sizeof(void*)*1);
v___x_3974_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_cls_3975_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
if (v_hasTrace_3973_ == 0)
{
v___y_3977_ = v_a_3929_;
v___y_3978_ = v_a_3930_;
goto v___jp_3976_;
}
else
{
lean_object* v___x_4079_; uint8_t v___x_4080_; 
v___x_4079_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4080_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3972_, v_options_3971_, v___x_4079_);
if (v___x_4080_ == 0)
{
v___y_3977_ = v_a_3929_;
v___y_3978_ = v_a_3930_;
goto v___jp_3976_;
}
else
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10);
v___x_4082_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3975_, v___x_4081_, v_a_3929_, v_a_3930_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_dec_ref_known(v___x_4082_, 1);
v___y_3977_ = v_a_3929_;
v___y_3978_ = v_a_3930_;
goto v___jp_3976_;
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec_ref(v_toSortArgs_3928_);
lean_dec_ref(v_sortedArgs_3926_);
lean_dec_ref(v_sortedDecls_3925_);
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4082_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4082_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
}
v___jp_3976_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; size_t v_sz_3982_; size_t v___x_3983_; lean_object* v___x_3984_; 
v___x_3979_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6);
v___x_3980_ = l_Array_toSubarray___redArg(v_sortedArgs_3926_, v___x_3968_, v___x_3959_);
v___x_3981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3979_);
lean_ctor_set(v___x_3981_, 1, v___x_3980_);
v_sz_3982_ = lean_array_size(v_sortedDecls_3925_);
v___x_3983_ = ((size_t)0ULL);
v___x_3984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_sortedDecls_3925_, v_sz_3982_, v___x_3983_, v___x_3981_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v_fst_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_4069_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v___x_3984_, 1);
v_fst_3986_ = lean_ctor_get(v_a_3985_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v_a_3985_);
if (v_isSharedCheck_4069_ == 0)
{
lean_object* v_unused_4070_; 
v_unused_4070_ = lean_ctor_get(v_a_3985_, 1);
lean_dec(v_unused_4070_);
v___x_3988_ = v_a_3985_;
v_isShared_3989_ = v_isSharedCheck_4069_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_fst_3986_);
lean_dec(v_a_3985_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_4069_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3990_ = l_Array_toSubarray___redArg(v_toSortArgs_3928_, v___x_3968_, v___x_3964_);
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 1, v___x_3990_);
v___x_3992_ = v___x_3988_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_fst_3986_);
lean_ctor_set(v_reuseFailAlloc_4068_, 1, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_4068_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
size_t v_sz_3993_; lean_object* v___x_3994_; 
v_sz_3993_ = lean_array_size(v_toSortDecls_3927_);
v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_toSortDecls_3927_, v_sz_3993_, v___x_3983_, v___x_3992_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v_fst_3996_; lean_object* v_size_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_a_3995_);
lean_dec_ref_known(v___x_3994_, 1);
v_fst_3996_ = lean_ctor_get(v_a_3995_, 0);
lean_inc_n(v_fst_3996_, 2);
lean_dec(v_a_3995_);
v_size_3997_ = lean_ctor_get(v_fst_3996_, 0);
v___x_3998_ = lean_mk_empty_array_with_capacity(v_size_3997_);
lean_inc_ref(v___x_3998_);
v___x_3999_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3974_);
lean_ctor_set(v___x_3999_, 1, v___x_3974_);
lean_ctor_set(v___x_3999_, 2, v___x_3998_);
lean_ctor_set(v___x_3999_, 3, v___x_3998_);
v___x_4000_ = lean_box(0);
v___x_4001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3996_, v_sortedDecls_3925_, v_sz_3982_, v___x_3983_, v___x_4000_, v___x_3999_, v___y_3977_, v___y_3978_);
lean_dec_ref(v_sortedDecls_3925_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v_snd_4003_; lean_object* v___x_4004_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref_known(v___x_4001_, 1);
v_snd_4003_ = lean_ctor_get(v_a_4002_, 1);
lean_inc(v_snd_4003_);
lean_dec(v_a_4002_);
v___x_4004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3996_, v_toSortDecls_3927_, v_sz_3993_, v___x_3983_, v___x_4000_, v_snd_4003_, v___y_3977_, v___y_3978_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v_snd_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4042_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
v_snd_4006_ = lean_ctor_get(v_a_4005_, 1);
v_isSharedCheck_4042_ = !lean_is_exclusive(v_a_4005_);
if (v_isSharedCheck_4042_ == 0)
{
lean_object* v_unused_4043_; 
v_unused_4043_ = lean_ctor_get(v_a_4005_, 0);
lean_dec(v_unused_4043_);
v___x_4008_ = v_a_4005_;
v_isShared_4009_ = v_isSharedCheck_4042_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_snd_4006_);
lean_dec(v_a_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4042_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v_toCold_4010_; lean_object* v_options_4011_; lean_object* v_newDecls_4012_; lean_object* v_newArgs_4013_; lean_object* v_inheritedTraceOptions_4014_; uint8_t v_hasTrace_4015_; lean_object* v___f_4016_; 
v_toCold_4010_ = lean_ctor_get(v___y_3977_, 0);
v_options_4011_ = lean_ctor_get(v_toCold_4010_, 2);
v_newDecls_4012_ = lean_ctor_get(v_snd_4006_, 2);
v_newArgs_4013_ = lean_ctor_get(v_snd_4006_, 3);
v_inheritedTraceOptions_4014_ = lean_ctor_get(v_toCold_4010_, 11);
v_hasTrace_4015_ = lean_ctor_get_uint8(v_options_4011_, sizeof(void*)*1);
lean_inc_ref(v_newArgs_4013_);
lean_inc_ref(v_newDecls_4012_);
v___f_4016_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4016_, 0, v_newDecls_4012_);
lean_closure_set(v___f_4016_, 1, v_newArgs_4013_);
if (v_hasTrace_4015_ == 0)
{
lean_del_object(v___x_4008_);
v___y_3952_ = v___f_4016_;
v___y_3953_ = v___y_3977_;
v___y_3954_ = v___y_3978_;
v___y_3955_ = v___x_4000_;
v_snd_3956_ = v_snd_4006_;
goto v___jp_3951_;
}
else
{
lean_object* v___x_4017_; uint8_t v___x_4018_; 
v___x_4017_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4018_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4014_, v_options_4011_, v___x_4017_);
if (v___x_4018_ == 0)
{
lean_del_object(v___x_4008_);
v___y_3952_ = v___f_4016_;
v___y_3953_ = v___y_3977_;
v___y_3954_ = v___y_3978_;
v___y_3955_ = v___x_4000_;
v_snd_3956_ = v_snd_4006_;
goto v___jp_3951_;
}
else
{
lean_object* v___x_4019_; size_t v_sz_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4027_; 
lean_inc_ref(v_newArgs_4013_);
lean_inc_ref_n(v_newDecls_4012_, 2);
lean_dec_ref(v___f_4016_);
v___x_4019_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8);
v_sz_4020_ = lean_array_size(v_newDecls_4012_);
v___x_4021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_4020_, v___x_3983_, v_newDecls_4012_);
v___x_4022_ = lean_array_to_list(v___x_4021_);
v___x_4023_ = lean_box(0);
v___x_4024_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v___x_4022_, v___x_4023_);
v___x_4025_ = l_Lean_MessageData_ofList(v___x_4024_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set_tag(v___x_4008_, 7);
lean_ctor_set(v___x_4008_, 1, v___x_4025_);
lean_ctor_set(v___x_4008_, 0, v___x_4019_);
v___x_4027_ = v___x_4008_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4019_);
lean_ctor_set(v_reuseFailAlloc_4041_, 1, v___x_4025_);
v___x_4027_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4028_; 
v___x_4028_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3975_, v___x_4027_, v_snd_4006_, v___y_3977_, v___y_3978_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v_fst_4030_; lean_object* v_snd_4031_; lean_object* v___x_4032_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref_known(v___x_4028_, 1);
v_fst_4030_ = lean_ctor_get(v_a_4029_, 0);
lean_inc(v_fst_4030_);
v_snd_4031_ = lean_ctor_get(v_a_4029_, 1);
lean_inc(v_snd_4031_);
lean_dec(v_a_4029_);
v___x_4032_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_4012_, v_newArgs_4013_, v_fst_4030_, v_snd_4031_, v___y_3977_, v___y_3978_);
v___y_3933_ = v___x_4032_;
goto v___jp_3932_;
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec_ref(v_newArgs_4013_);
lean_dec_ref(v_newDecls_4012_);
v_a_4033_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4028_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4028_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
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
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
v_a_4044_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4004_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4004_);
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
else
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_dec(v_fst_3996_);
v_a_4052_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_4001_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4001_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
lean_dec_ref(v_sortedDecls_3925_);
v_a_4060_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_3994_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_3994_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec_ref(v_toSortArgs_3928_);
lean_dec_ref(v_sortedDecls_3925_);
v_a_4071_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_3984_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_3984_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
}
else
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
lean_dec_ref(v_toSortArgs_3928_);
v___x_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4091_, 0, v_sortedDecls_3925_);
lean_ctor_set(v___x_4091_, 1, v_sortedArgs_3926_);
v___x_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
return v___x_4092_;
}
}
}
v___jp_3932_:
{
if (lean_obj_tag(v___y_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3942_; 
v_a_3934_ = lean_ctor_get(v___y_3933_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___y_3933_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3936_ = v___y_3933_;
v_isShared_3937_ = v_isSharedCheck_3942_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___y_3933_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3942_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v_fst_3938_; lean_object* v___x_3940_; 
v_fst_3938_ = lean_ctor_get(v_a_3934_, 0);
lean_inc(v_fst_3938_);
lean_dec(v_a_3934_);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 0, v_fst_3938_);
v___x_3940_ = v___x_3936_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_fst_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
v_a_3943_ = lean_ctor_get(v___y_3933_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___y_3933_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___y_3933_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___y_3933_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
v___jp_3951_:
{
lean_object* v___x_3957_; 
lean_inc(v___y_3954_);
lean_inc_ref(v___y_3953_);
v___x_3957_ = lean_apply_5(v___y_3952_, v___y_3955_, v_snd_3956_, v___y_3953_, v___y_3954_, lean_box(0));
v___y_3933_ = v___x_3957_;
goto v___jp_3932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object* v_sortedDecls_4093_, lean_object* v_sortedArgs_4094_, lean_object* v_toSortDecls_4095_, lean_object* v_toSortArgs_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v_sortedDecls_4093_, v_sortedArgs_4094_, v_toSortDecls_4095_, v_toSortArgs_4096_, v_a_4097_, v_a_4098_);
lean_dec(v_a_4098_);
lean_dec_ref(v_a_4097_);
lean_dec_ref(v_toSortDecls_4095_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object* v_00_u03b2_4101_, lean_object* v_m_4102_, lean_object* v_a_4103_, lean_object* v_b_4104_){
_start:
{
lean_object* v___x_4105_; 
v___x_4105_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(v_m_4102_, v_a_4103_, v_b_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object* v_as_4106_, size_t v_sz_4107_, size_t v_i_4108_, lean_object* v_b_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v___x_4113_; 
v___x_4113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_4106_, v_sz_4107_, v_i_4108_, v_b_4109_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object* v_as_4114_, lean_object* v_sz_4115_, lean_object* v_i_4116_, lean_object* v_b_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
size_t v_sz_boxed_4121_; size_t v_i_boxed_4122_; lean_object* v_res_4123_; 
v_sz_boxed_4121_ = lean_unbox_usize(v_sz_4115_);
lean_dec(v_sz_4115_);
v_i_boxed_4122_ = lean_unbox_usize(v_i_4116_);
lean_dec(v_i_4116_);
v_res_4123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_as_4114_, v_sz_boxed_4121_, v_i_boxed_4122_, v_b_4117_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec_ref(v_as_4114_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0(lean_object* v_00_u03b2_4124_, lean_object* v_a_4125_, lean_object* v_b_4126_, lean_object* v_x_4127_){
_start:
{
lean_object* v___x_4128_; 
v___x_4128_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_4125_, v_b_4126_, v_x_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(lean_object* v_msg_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v___f_4136_; lean_object* v___x_1735__overap_4137_; lean_object* v___x_4138_; 
v___f_4136_ = ((lean_object*)(l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1___closed__0));
v___x_1735__overap_4137_ = lean_panic_fn_borrowed(v___f_4136_, v_msg_4130_);
lean_inc(v___y_4134_);
lean_inc_ref(v___y_4133_);
lean_inc(v___y_4132_);
lean_inc_ref(v___y_4131_);
v___x_4138_ = lean_apply_5(v___x_1735__overap_4137_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, lean_box(0));
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1___boxed(lean_object* v_msg_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(v_msg_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
return v_res_4145_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(lean_object* v_as_4146_, size_t v_i_4147_, size_t v_stop_4148_){
_start:
{
uint8_t v___x_4153_; 
v___x_4153_ = lean_usize_dec_eq(v_i_4147_, v_stop_4148_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; 
v___x_4154_ = lean_array_uget_borrowed(v_as_4146_, v_i_4147_);
if (lean_obj_tag(v___x_4154_) == 0)
{
goto v___jp_4149_;
}
else
{
lean_object* v_val_4155_; uint8_t v___x_4156_; 
v_val_4155_ = lean_ctor_get(v___x_4154_, 0);
v___x_4156_ = l_Lean_LocalDecl_isLet(v_val_4155_, v___x_4153_);
if (v___x_4156_ == 0)
{
goto v___jp_4149_;
}
else
{
return v___x_4156_;
}
}
}
else
{
uint8_t v___x_4157_; 
v___x_4157_ = 0;
return v___x_4157_;
}
v___jp_4149_:
{
size_t v___x_4150_; size_t v___x_4151_; 
v___x_4150_ = ((size_t)1ULL);
v___x_4151_ = lean_usize_add(v_i_4147_, v___x_4150_);
v_i_4147_ = v___x_4151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1___boxed(lean_object* v_as_4158_, lean_object* v_i_4159_, lean_object* v_stop_4160_){
_start:
{
size_t v_i_boxed_4161_; size_t v_stop_boxed_4162_; uint8_t v_res_4163_; lean_object* v_r_4164_; 
v_i_boxed_4161_ = lean_unbox_usize(v_i_4159_);
lean_dec(v_i_4159_);
v_stop_boxed_4162_ = lean_unbox_usize(v_stop_4160_);
lean_dec(v_stop_4160_);
v_res_4163_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_as_4158_, v_i_boxed_4161_, v_stop_boxed_4162_);
lean_dec_ref(v_as_4158_);
v_r_4164_ = lean_box(v_res_4163_);
return v_r_4164_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(lean_object* v_x_4165_){
_start:
{
if (lean_obj_tag(v_x_4165_) == 0)
{
lean_object* v_cs_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; 
v_cs_4166_ = lean_ctor_get(v_x_4165_, 0);
v___x_4167_ = lean_unsigned_to_nat(0u);
v___x_4168_ = lean_array_get_size(v_cs_4166_);
v___x_4169_ = lean_nat_dec_lt(v___x_4167_, v___x_4168_);
if (v___x_4169_ == 0)
{
return v___x_4169_;
}
else
{
size_t v___x_4170_; size_t v___x_4171_; uint8_t v___x_4172_; 
v___x_4170_ = ((size_t)0ULL);
v___x_4171_ = lean_usize_of_nat(v___x_4168_);
v___x_4172_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(v_cs_4166_, v___x_4170_, v___x_4171_);
return v___x_4172_;
}
}
else
{
lean_object* v_vs_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; 
v_vs_4173_ = lean_ctor_get(v_x_4165_, 0);
v___x_4174_ = lean_unsigned_to_nat(0u);
v___x_4175_ = lean_array_get_size(v_vs_4173_);
v___x_4176_ = lean_nat_dec_lt(v___x_4174_, v___x_4175_);
if (v___x_4176_ == 0)
{
return v___x_4176_;
}
else
{
size_t v___x_4177_; size_t v___x_4178_; uint8_t v___x_4179_; 
v___x_4177_ = ((size_t)0ULL);
v___x_4178_ = lean_usize_of_nat(v___x_4175_);
v___x_4179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_vs_4173_, v___x_4177_, v___x_4178_);
return v___x_4179_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(lean_object* v_as_4180_, size_t v_i_4181_, size_t v_stop_4182_){
_start:
{
uint8_t v___x_4183_; 
v___x_4183_ = lean_usize_dec_eq(v_i_4181_, v_stop_4182_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4184_; uint8_t v___x_4185_; 
v___x_4184_ = lean_array_uget_borrowed(v_as_4180_, v_i_4181_);
v___x_4185_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v___x_4184_);
if (v___x_4185_ == 0)
{
size_t v___x_4186_; size_t v___x_4187_; 
v___x_4186_ = ((size_t)1ULL);
v___x_4187_ = lean_usize_add(v_i_4181_, v___x_4186_);
v_i_4181_ = v___x_4187_;
goto _start;
}
else
{
return v___x_4185_;
}
}
else
{
uint8_t v___x_4189_; 
v___x_4189_ = 0;
return v___x_4189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4190_, lean_object* v_i_4191_, lean_object* v_stop_4192_){
_start:
{
size_t v_i_boxed_4193_; size_t v_stop_boxed_4194_; uint8_t v_res_4195_; lean_object* v_r_4196_; 
v_i_boxed_4193_ = lean_unbox_usize(v_i_4191_);
lean_dec(v_i_4191_);
v_stop_boxed_4194_ = lean_unbox_usize(v_stop_4192_);
lean_dec(v_stop_4192_);
v_res_4195_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(v_as_4190_, v_i_boxed_4193_, v_stop_boxed_4194_);
lean_dec_ref(v_as_4190_);
v_r_4196_ = lean_box(v_res_4195_);
return v_r_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0___boxed(lean_object* v_x_4197_){
_start:
{
uint8_t v_res_4198_; lean_object* v_r_4199_; 
v_res_4198_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v_x_4197_);
lean_dec_ref(v_x_4197_);
v_r_4199_ = lean_box(v_res_4198_);
return v_r_4199_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object* v_t_4200_){
_start:
{
lean_object* v_root_4201_; lean_object* v_tail_4202_; uint8_t v___x_4203_; 
v_root_4201_ = lean_ctor_get(v_t_4200_, 0);
v_tail_4202_ = lean_ctor_get(v_t_4200_, 1);
v___x_4203_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v_root_4201_);
if (v___x_4203_ == 0)
{
lean_object* v___x_4204_; lean_object* v___x_4205_; uint8_t v___x_4206_; 
v___x_4204_ = lean_unsigned_to_nat(0u);
v___x_4205_ = lean_array_get_size(v_tail_4202_);
v___x_4206_ = lean_nat_dec_lt(v___x_4204_, v___x_4205_);
if (v___x_4206_ == 0)
{
return v___x_4206_;
}
else
{
size_t v___x_4207_; size_t v___x_4208_; uint8_t v___x_4209_; 
v___x_4207_ = ((size_t)0ULL);
v___x_4208_ = lean_usize_of_nat(v___x_4205_);
v___x_4209_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_tail_4202_, v___x_4207_, v___x_4208_);
return v___x_4209_;
}
}
else
{
return v___x_4203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object* v_t_4210_){
_start:
{
uint8_t v_res_4211_; lean_object* v_r_4212_; 
v_res_4211_ = l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_t_4210_);
lean_dec_ref(v_t_4210_);
v_r_4212_ = lean_box(v_res_4211_);
return v_r_4212_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0(void){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4213_ = lean_box(0);
v___x_4214_ = lean_unsigned_to_nat(16u);
v___x_4215_ = lean_mk_array(v___x_4214_, v___x_4213_);
return v___x_4215_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1(void){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4216_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0);
v___x_4217_ = lean_unsigned_to_nat(0u);
v___x_4218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4217_);
lean_ctor_set(v___x_4218_, 1, v___x_4216_);
return v___x_4218_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3(void){
_start:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4221_ = lean_unsigned_to_nat(1u);
v___x_4222_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2));
v___x_4223_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
v___x_4224_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4223_);
lean_ctor_set(v___x_4224_, 1, v___x_4223_);
lean_ctor_set(v___x_4224_, 2, v___x_4222_);
lean_ctor_set(v___x_4224_, 3, v___x_4221_);
lean_ctor_set(v___x_4224_, 4, v___x_4222_);
lean_ctor_set(v___x_4224_, 5, v___x_4222_);
lean_ctor_set(v___x_4224_, 6, v___x_4222_);
lean_ctor_set(v___x_4224_, 7, v___x_4222_);
lean_ctor_set(v___x_4224_, 8, v___x_4221_);
lean_ctor_set(v___x_4224_, 9, v___x_4222_);
lean_ctor_set(v___x_4224_, 10, v___x_4222_);
lean_ctor_set(v___x_4224_, 11, v___x_4222_);
return v___x_4224_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6(void){
_start:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4227_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5));
v___x_4228_ = lean_unsigned_to_nat(2u);
v___x_4229_ = lean_unsigned_to_nat(424u);
v___x_4230_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__4));
v___x_4231_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_4232_ = l_mkPanicMessageWithDecl(v___x_4231_, v___x_4230_, v___x_4229_, v___x_4228_, v___x_4227_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* v_type_4233_, lean_object* v_value_4234_, uint8_t v_zetaDelta_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v_lctx_4241_; lean_object* v_decls_4242_; uint8_t v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v_lctx_4241_ = lean_ctor_get(v_a_4236_, 2);
v_decls_4242_ = lean_ctor_get(v_lctx_4241_, 1);
v___x_4243_ = l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_decls_4242_);
v___x_4244_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4244_, 0, v_zetaDelta_4235_);
lean_ctor_set_uint8(v___x_4244_, 1, v___x_4243_);
v___x_4245_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__3, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3);
v___x_4246_ = lean_st_mk_ref(v___x_4245_);
v___x_4247_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_4233_, v_value_4234_, v___x_4244_, v___x_4246_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
lean_dec_ref_known(v___x_4244_, 0);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v_a_4248_; lean_object* v___x_4249_; lean_object* v_fst_4250_; lean_object* v_snd_4251_; lean_object* v_levelParams_4252_; lean_object* v_levelArgs_4253_; lean_object* v_newLocalDecls_4254_; lean_object* v_newLocalDeclsForMVars_4255_; lean_object* v_newLetDecls_4256_; lean_object* v_exprMVarArgs_4257_; lean_object* v_exprFVarArgs_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4248_);
lean_dec_ref_known(v___x_4247_, 1);
v___x_4249_ = lean_st_ref_get(v___x_4246_);
lean_dec(v___x_4246_);
v_fst_4250_ = lean_ctor_get(v_a_4248_, 0);
lean_inc(v_fst_4250_);
v_snd_4251_ = lean_ctor_get(v_a_4248_, 1);
lean_inc(v_snd_4251_);
lean_dec(v_a_4248_);
v_levelParams_4252_ = lean_ctor_get(v___x_4249_, 2);
lean_inc_ref(v_levelParams_4252_);
v_levelArgs_4253_ = lean_ctor_get(v___x_4249_, 4);
lean_inc_ref(v_levelArgs_4253_);
v_newLocalDecls_4254_ = lean_ctor_get(v___x_4249_, 5);
lean_inc_ref(v_newLocalDecls_4254_);
v_newLocalDeclsForMVars_4255_ = lean_ctor_get(v___x_4249_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_4255_);
v_newLetDecls_4256_ = lean_ctor_get(v___x_4249_, 7);
lean_inc_ref(v_newLetDecls_4256_);
v_exprMVarArgs_4257_ = lean_ctor_get(v___x_4249_, 9);
lean_inc_ref(v_exprMVarArgs_4257_);
v_exprFVarArgs_4258_ = lean_ctor_get(v___x_4249_, 10);
lean_inc_ref(v_exprFVarArgs_4258_);
lean_dec(v___x_4249_);
v___x_4259_ = l_Array_reverse___redArg(v_newLocalDecls_4254_);
v___x_4260_ = l_Array_reverse___redArg(v_exprFVarArgs_4258_);
v___x_4261_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v___x_4259_, v___x_4260_, v_newLocalDeclsForMVars_4255_, v_exprMVarArgs_4257_, v_a_4238_, v_a_4239_);
lean_dec_ref(v_newLocalDeclsForMVars_4255_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4280_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4264_ = v___x_4261_;
v_isShared_4265_ = v_isSharedCheck_4280_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4261_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4280_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v_fst_4266_; lean_object* v_snd_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; uint8_t v___x_4273_; 
v_fst_4266_ = lean_ctor_get(v_a_4262_, 0);
lean_inc_n(v_fst_4266_, 2);
v_snd_4267_ = lean_ctor_get(v_a_4262_, 1);
lean_inc(v_snd_4267_);
lean_dec(v_a_4262_);
v___x_4268_ = l_Array_reverse___redArg(v_newLetDecls_4256_);
lean_inc_ref(v___x_4268_);
v___x_4269_ = l_Lean_Meta_Closure_mkForall(v___x_4268_, v_fst_4250_);
lean_dec(v_fst_4250_);
v___x_4270_ = l_Lean_Meta_Closure_mkForall(v_fst_4266_, v___x_4269_);
lean_dec_ref(v___x_4269_);
v___x_4271_ = l_Lean_Meta_Closure_mkLambda(v___x_4268_, v_snd_4251_);
lean_dec(v_snd_4251_);
v___x_4272_ = l_Lean_Meta_Closure_mkLambda(v_fst_4266_, v___x_4271_);
lean_dec_ref(v___x_4271_);
v___x_4273_ = l_Lean_Expr_hasFVar(v___x_4272_);
if (v___x_4273_ == 0)
{
lean_object* v___x_4274_; lean_object* v___x_4276_; 
v___x_4274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4274_, 0, v_levelParams_4252_);
lean_ctor_set(v___x_4274_, 1, v___x_4270_);
lean_ctor_set(v___x_4274_, 2, v___x_4272_);
lean_ctor_set(v___x_4274_, 3, v_levelArgs_4253_);
lean_ctor_set(v___x_4274_, 4, v_snd_4267_);
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 0, v___x_4274_);
v___x_4276_ = v___x_4264_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
else
{
lean_object* v___x_4278_; lean_object* v___x_4279_; 
lean_dec_ref(v___x_4272_);
lean_dec_ref(v___x_4270_);
lean_dec(v_snd_4267_);
lean_del_object(v___x_4264_);
lean_dec_ref(v_levelArgs_4253_);
lean_dec_ref(v_levelParams_4252_);
v___x_4278_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__6, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6);
v___x_4279_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(v___x_4278_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
return v___x_4279_;
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec_ref(v_newLetDecls_4256_);
lean_dec_ref(v_levelArgs_4253_);
lean_dec_ref(v_levelParams_4252_);
lean_dec(v_snd_4251_);
lean_dec(v_fst_4250_);
v_a_4281_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4261_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4261_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec(v___x_4246_);
v_a_4289_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4247_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4247_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* v_type_4297_, lean_object* v_value_4298_, lean_object* v_zetaDelta_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
uint8_t v_zetaDelta_boxed_4305_; lean_object* v_res_4306_; 
v_zetaDelta_boxed_4305_ = lean_unbox(v_zetaDelta_4299_);
v_res_4306_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4297_, v_value_4298_, v_zetaDelta_boxed_4305_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_);
lean_dec(v_a_4303_);
lean_dec_ref(v_a_4302_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* v_name_4307_, lean_object* v_levelParams_4308_, lean_object* v_type_4309_, lean_object* v_value_4310_, lean_object* v_hints_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___x_4314_; uint8_t v___y_4316_; lean_object* v_env_4324_; uint8_t v___x_4325_; 
v___x_4314_ = lean_st_ref_get(v___y_4312_);
v_env_4324_ = lean_ctor_get(v___x_4314_, 0);
lean_inc_ref_n(v_env_4324_, 2);
lean_dec(v___x_4314_);
v___x_4325_ = l_Lean_Environment_hasUnsafe(v_env_4324_, v_type_4309_);
if (v___x_4325_ == 0)
{
uint8_t v___x_4326_; 
v___x_4326_ = l_Lean_Environment_hasUnsafe(v_env_4324_, v_value_4310_);
if (v___x_4326_ == 0)
{
uint8_t v___x_4327_; 
v___x_4327_ = 1;
v___y_4316_ = v___x_4327_;
goto v___jp_4315_;
}
else
{
goto v___jp_4322_;
}
}
else
{
lean_dec_ref(v_env_4324_);
goto v___jp_4322_;
}
v___jp_4315_:
{
lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
lean_inc(v_name_4307_);
v___x_4317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4317_, 0, v_name_4307_);
lean_ctor_set(v___x_4317_, 1, v_levelParams_4308_);
lean_ctor_set(v___x_4317_, 2, v_type_4309_);
v___x_4318_ = lean_box(0);
v___x_4319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4319_, 0, v_name_4307_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4320_, 0, v___x_4317_);
lean_ctor_set(v___x_4320_, 1, v_value_4310_);
lean_ctor_set(v___x_4320_, 2, v_hints_4311_);
lean_ctor_set(v___x_4320_, 3, v___x_4319_);
lean_ctor_set_uint8(v___x_4320_, sizeof(void*)*4, v___y_4316_);
v___x_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4320_);
return v___x_4321_;
}
v___jp_4322_:
{
uint8_t v___x_4323_; 
v___x_4323_ = 0;
v___y_4316_ = v___x_4323_;
goto v___jp_4315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* v_name_4328_, lean_object* v_levelParams_4329_, lean_object* v_type_4330_, lean_object* v_value_4331_, lean_object* v_hints_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4328_, v_levelParams_4329_, v_type_4330_, v_value_4331_, v_hints_4332_, v___y_4333_);
lean_dec(v___y_4333_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(lean_object* v_name_4336_, lean_object* v_levelParams_4337_, lean_object* v_type_4338_, lean_object* v_value_4339_, lean_object* v_hints_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v___x_4346_; 
v___x_4346_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4336_, v_levelParams_4337_, v_type_4338_, v_value_4339_, v_hints_4340_, v___y_4344_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* v_name_4347_, lean_object* v_levelParams_4348_, lean_object* v_type_4349_, lean_object* v_value_4350_, lean_object* v_hints_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(v_name_4347_, v_levelParams_4348_, v_type_4349_, v_value_4350_, v_hints_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* v_name_4358_, lean_object* v_type_4359_, lean_object* v_value_4360_, uint8_t v_zetaDelta_4361_, uint8_t v_compile_4362_, uint8_t v_logCompileErrors_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4359_, v_value_4360_, v_zetaDelta_4361_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4421_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4372_ = v___x_4369_;
v_isShared_4373_ = v_isSharedCheck_4421_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4369_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4421_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4383_; lean_object* v_env_4384_; lean_object* v_levelParams_4385_; lean_object* v_type_4386_; lean_object* v_value_4387_; uint32_t v___x_4388_; uint32_t v___x_4389_; uint32_t v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4420_; 
v___x_4383_ = lean_st_ref_get(v_a_4367_);
v_env_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc_ref(v_env_4384_);
lean_dec(v___x_4383_);
v_levelParams_4385_ = lean_ctor_get(v_a_4370_, 0);
v_type_4386_ = lean_ctor_get(v_a_4370_, 1);
v_value_4387_ = lean_ctor_get(v_a_4370_, 2);
lean_inc_ref_n(v_value_4387_, 2);
v___x_4388_ = l_Lean_getMaxHeight(v_env_4384_, v_value_4387_);
v___x_4389_ = 1;
v___x_4390_ = lean_uint32_add(v___x_4388_, v___x_4389_);
v___x_4391_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4391_, 0, v___x_4390_);
lean_inc_ref(v_levelParams_4385_);
v___x_4392_ = lean_array_to_list(v_levelParams_4385_);
lean_inc_ref(v_type_4386_);
lean_inc(v_name_4358_);
v___x_4393_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4358_, v___x_4392_, v_type_4386_, v_value_4387_, v___x_4391_, v_a_4367_);
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4396_ = v___x_4393_;
v_isShared_4397_ = v_isSharedCheck_4420_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4393_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4420_;
goto v_resetjp_4395_;
}
v___jp_4374_:
{
lean_object* v_levelArgs_4375_; lean_object* v_exprArgs_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4381_; 
v_levelArgs_4375_ = lean_ctor_get(v_a_4370_, 3);
lean_inc_ref(v_levelArgs_4375_);
v_exprArgs_4376_ = lean_ctor_get(v_a_4370_, 4);
lean_inc_ref(v_exprArgs_4376_);
lean_dec(v_a_4370_);
v___x_4377_ = lean_array_to_list(v_levelArgs_4375_);
v___x_4378_ = l_Lean_mkConst(v_name_4358_, v___x_4377_);
v___x_4379_ = l_Lean_mkAppN(v___x_4378_, v_exprArgs_4376_);
lean_dec_ref(v_exprArgs_4376_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 0, v___x_4379_);
v___x_4381_ = v___x_4372_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
lean_ctor_set_tag(v___x_4396_, 1);
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
uint8_t v___x_4400_; lean_object* v___x_4401_; 
v___x_4400_ = 0;
lean_inc_ref(v___x_4399_);
v___x_4401_ = l_Lean_addDecl(v___x_4399_, v___x_4400_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_dec_ref_known(v___x_4401_, 1);
if (v_compile_4362_ == 0)
{
lean_dec_ref(v___x_4399_);
goto v___jp_4374_;
}
else
{
lean_object* v___x_4402_; 
v___x_4402_ = l_Lean_compileDecl(v___x_4399_, v_logCompileErrors_4363_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_dec_ref_known(v___x_4402_, 1);
goto v___jp_4374_;
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_del_object(v___x_4372_);
lean_dec(v_a_4370_);
lean_dec(v_name_4358_);
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4402_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4402_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec_ref(v___x_4399_);
lean_del_object(v___x_4372_);
lean_dec(v_a_4370_);
lean_dec(v_name_4358_);
v_a_4411_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4401_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4401_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
lean_dec(v_name_4358_);
v_a_4422_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4369_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4369_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* v_name_4430_, lean_object* v_type_4431_, lean_object* v_value_4432_, lean_object* v_zetaDelta_4433_, lean_object* v_compile_4434_, lean_object* v_logCompileErrors_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_){
_start:
{
uint8_t v_zetaDelta_boxed_4441_; uint8_t v_compile_boxed_4442_; uint8_t v_logCompileErrors_boxed_4443_; lean_object* v_res_4444_; 
v_zetaDelta_boxed_4441_ = lean_unbox(v_zetaDelta_4433_);
v_compile_boxed_4442_ = lean_unbox(v_compile_4434_);
v_logCompileErrors_boxed_4443_ = lean_unbox(v_logCompileErrors_4435_);
v_res_4444_ = l_Lean_Meta_mkAuxDefinition(v_name_4430_, v_type_4431_, v_value_4432_, v_zetaDelta_boxed_4441_, v_compile_boxed_4442_, v_logCompileErrors_boxed_4443_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_);
lean_dec(v_a_4439_);
lean_dec_ref(v_a_4438_);
lean_dec(v_a_4437_);
lean_dec_ref(v_a_4436_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* v_name_4445_, lean_object* v_value_4446_, uint8_t v_zetaDelta_4447_, uint8_t v_compile_4448_, uint8_t v_logCompileErrors_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v___x_4455_; 
lean_inc(v_a_4453_);
lean_inc_ref(v_a_4452_);
lean_inc(v_a_4451_);
lean_inc_ref(v_a_4450_);
lean_inc_ref(v_value_4446_);
v___x_4455_ = lean_infer_type(v_value_4446_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_a_4456_);
lean_dec_ref_known(v___x_4455_, 1);
v___x_4457_ = l_Lean_Expr_headBeta(v_a_4456_);
v___x_4458_ = l_Lean_Meta_mkAuxDefinition(v_name_4445_, v___x_4457_, v_value_4446_, v_zetaDelta_4447_, v_compile_4448_, v_logCompileErrors_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
return v___x_4458_;
}
else
{
lean_dec_ref(v_value_4446_);
lean_dec(v_name_4445_);
return v___x_4455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* v_name_4459_, lean_object* v_value_4460_, lean_object* v_zetaDelta_4461_, lean_object* v_compile_4462_, lean_object* v_logCompileErrors_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_){
_start:
{
uint8_t v_zetaDelta_boxed_4469_; uint8_t v_compile_boxed_4470_; uint8_t v_logCompileErrors_boxed_4471_; lean_object* v_res_4472_; 
v_zetaDelta_boxed_4469_ = lean_unbox(v_zetaDelta_4461_);
v_compile_boxed_4470_ = lean_unbox(v_compile_4462_);
v_logCompileErrors_boxed_4471_ = lean_unbox(v_logCompileErrors_4463_);
v_res_4472_ = l_Lean_Meta_mkAuxDefinitionFor(v_name_4459_, v_value_4460_, v_zetaDelta_boxed_4469_, v_compile_boxed_4470_, v_logCompileErrors_boxed_4471_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
lean_dec(v_a_4465_);
lean_dec_ref(v_a_4464_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* v_type_4473_, lean_object* v_value_4474_, uint8_t v_zetaDelta_4475_, lean_object* v_kind_x3f_4476_, uint8_t v_cache_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4473_, v_value_4474_, v_zetaDelta_4475_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v_levelParams_4485_; lean_object* v_type_4486_; lean_object* v_value_4487_; lean_object* v_levelArgs_4488_; lean_object* v_exprArgs_4489_; lean_object* v___x_4490_; uint8_t v___x_4491_; lean_object* v___x_4492_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4483_, 1);
v_levelParams_4485_ = lean_ctor_get(v_a_4484_, 0);
lean_inc_ref(v_levelParams_4485_);
v_type_4486_ = lean_ctor_get(v_a_4484_, 1);
lean_inc_ref(v_type_4486_);
v_value_4487_ = lean_ctor_get(v_a_4484_, 2);
lean_inc_ref(v_value_4487_);
v_levelArgs_4488_ = lean_ctor_get(v_a_4484_, 3);
lean_inc_ref(v_levelArgs_4488_);
v_exprArgs_4489_ = lean_ctor_get(v_a_4484_, 4);
lean_inc_ref(v_exprArgs_4489_);
lean_dec(v_a_4484_);
v___x_4490_ = lean_array_to_list(v_levelParams_4485_);
v___x_4491_ = 0;
v___x_4492_ = l_Lean_Meta_mkAuxLemma(v___x_4490_, v_type_4486_, v_value_4487_, v_kind_x3f_4476_, v_cache_4477_, v___x_4491_, v___x_4491_, v___x_4491_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4503_; 
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4495_ = v___x_4492_;
v_isShared_4496_ = v_isSharedCheck_4503_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4492_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4503_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4501_; 
v___x_4497_ = lean_array_to_list(v_levelArgs_4488_);
v___x_4498_ = l_Lean_mkConst(v_a_4493_, v___x_4497_);
v___x_4499_ = l_Lean_mkAppN(v___x_4498_, v_exprArgs_4489_);
lean_dec_ref(v_exprArgs_4489_);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v___x_4499_);
v___x_4501_ = v___x_4495_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4499_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec_ref(v_exprArgs_4489_);
lean_dec_ref(v_levelArgs_4488_);
v_a_4504_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4492_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4492_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
lean_dec(v_kind_x3f_4476_);
v_a_4512_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4483_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4483_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* v_type_4520_, lean_object* v_value_4521_, lean_object* v_zetaDelta_4522_, lean_object* v_kind_x3f_4523_, lean_object* v_cache_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_){
_start:
{
uint8_t v_zetaDelta_boxed_4530_; uint8_t v_cache_boxed_4531_; lean_object* v_res_4532_; 
v_zetaDelta_boxed_4530_ = lean_unbox(v_zetaDelta_4522_);
v_cache_boxed_4531_ = lean_unbox(v_cache_4524_);
v_res_4532_ = l_Lean_Meta_mkAuxTheorem(v_type_4520_, v_value_4521_, v_zetaDelta_boxed_4530_, v_kind_x3f_4523_, v_cache_boxed_4531_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec(v_a_4526_);
lean_dec_ref(v_a_4525_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4588_; uint8_t v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4588_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_4589_ = 0;
v___x_4590_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_));
v___x_4591_ = l_Lean_registerTraceClass(v___x_4588_, v___x_4589_, v___x_4590_);
return v___x_4591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(lean_object* v_a_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
return v_res_4593_;
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
