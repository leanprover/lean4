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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0(void){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2582_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
return v___x_2584_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_2586_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
lean_ctor_set(v___x_2586_, 2, v___x_2585_);
lean_ctor_set(v___x_2586_, 3, v___x_2585_);
lean_ctor_set(v___x_2586_, 4, v___x_2585_);
lean_ctor_set(v___x_2586_, 5, v___x_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* v_type_2587_, lean_object* v_value_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v_cache_2598_; lean_object* v_a_2600_; lean_object* v___x_2611_; lean_object* v_mctx_2612_; lean_object* v_zetaDeltaFVarIds_2613_; lean_object* v_postponed_2614_; lean_object* v_diag_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2681_; 
v___x_2596_ = lean_box(1);
v___x_2597_ = lean_st_ref_get(v_a_2592_);
v_cache_2598_ = lean_ctor_get(v___x_2597_, 1);
lean_inc_ref(v_cache_2598_);
lean_dec(v___x_2597_);
v___x_2611_ = lean_st_ref_take(v_a_2592_);
v_mctx_2612_ = lean_ctor_get(v___x_2611_, 0);
v_zetaDeltaFVarIds_2613_ = lean_ctor_get(v___x_2611_, 2);
v_postponed_2614_ = lean_ctor_get(v___x_2611_, 3);
v_diag_2615_ = lean_ctor_get(v___x_2611_, 4);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; 
v_unused_2682_ = lean_ctor_get(v___x_2611_, 1);
lean_dec(v_unused_2682_);
v___x_2617_ = v___x_2611_;
v_isShared_2618_ = v_isSharedCheck_2681_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_diag_2615_);
lean_inc(v_postponed_2614_);
lean_inc(v_zetaDeltaFVarIds_2613_);
lean_inc(v_mctx_2612_);
lean_dec(v___x_2611_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2681_;
goto v_resetjp_2616_;
}
v___jp_2599_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
v___x_2601_ = lean_box(0);
v___x_2602_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2592_, v_cache_2598_, v___x_2601_);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2609_ == 0)
{
lean_object* v_unused_2610_; 
v_unused_2610_ = lean_ctor_get(v___x_2602_, 0);
lean_dec(v_unused_2610_);
v___x_2604_ = v___x_2602_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_dec(v___x_2602_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set_tag(v___x_2604_, 1);
lean_ctor_set(v___x_2604_, 0, v_a_2600_);
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2600_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2619_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 1, v___x_2619_);
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_mctx_2612_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_zetaDeltaFVarIds_2613_);
lean_ctor_set(v_reuseFailAlloc_2680_, 3, v_postponed_2614_);
lean_ctor_set(v_reuseFailAlloc_2680_, 4, v_diag_2615_);
v___x_2621_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; lean_object* v_keyedConfig_2623_; lean_object* v_zetaDeltaSet_2624_; lean_object* v_lctx_2625_; lean_object* v_localInstances_2626_; lean_object* v_defEqCtx_x3f_2627_; lean_object* v_synthPendingDepth_2628_; lean_object* v_customCanUnfoldPredicate_x3f_2629_; uint8_t v_univApprox_2630_; uint8_t v_inTypeClassResolution_2631_; uint8_t v_cacheInferType_2632_; uint8_t v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v_mctx_2636_; lean_object* v_cache_2637_; lean_object* v_zetaDeltaFVarIds_2638_; lean_object* v_postponed_2639_; lean_object* v_diag_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2679_; 
v___x_2622_ = lean_st_ref_put(v_a_2592_, v___x_2621_);
v_keyedConfig_2623_ = lean_ctor_get(v_a_2591_, 0);
v_zetaDeltaSet_2624_ = lean_ctor_get(v_a_2591_, 1);
v_lctx_2625_ = lean_ctor_get(v_a_2591_, 2);
v_localInstances_2626_ = lean_ctor_get(v_a_2591_, 3);
v_defEqCtx_x3f_2627_ = lean_ctor_get(v_a_2591_, 4);
v_synthPendingDepth_2628_ = lean_ctor_get(v_a_2591_, 5);
v_customCanUnfoldPredicate_x3f_2629_ = lean_ctor_get(v_a_2591_, 6);
v_univApprox_2630_ = lean_ctor_get_uint8(v_a_2591_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2631_ = lean_ctor_get_uint8(v_a_2591_, sizeof(void*)*7 + 2);
v_cacheInferType_2632_ = lean_ctor_get_uint8(v_a_2591_, sizeof(void*)*7 + 3);
v___x_2633_ = 1;
lean_inc(v_customCanUnfoldPredicate_x3f_2629_);
lean_inc(v_synthPendingDepth_2628_);
lean_inc(v_defEqCtx_x3f_2627_);
lean_inc_ref(v_localInstances_2626_);
lean_inc_ref(v_lctx_2625_);
lean_inc(v_zetaDeltaSet_2624_);
lean_inc_ref(v_keyedConfig_2623_);
v___x_2634_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2634_, 0, v_keyedConfig_2623_);
lean_ctor_set(v___x_2634_, 1, v_zetaDeltaSet_2624_);
lean_ctor_set(v___x_2634_, 2, v_lctx_2625_);
lean_ctor_set(v___x_2634_, 3, v_localInstances_2626_);
lean_ctor_set(v___x_2634_, 4, v_defEqCtx_x3f_2627_);
lean_ctor_set(v___x_2634_, 5, v_synthPendingDepth_2628_);
lean_ctor_set(v___x_2634_, 6, v_customCanUnfoldPredicate_x3f_2629_);
lean_ctor_set_uint8(v___x_2634_, sizeof(void*)*7, v___x_2633_);
lean_ctor_set_uint8(v___x_2634_, sizeof(void*)*7 + 1, v_univApprox_2630_);
lean_ctor_set_uint8(v___x_2634_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2631_);
lean_ctor_set_uint8(v___x_2634_, sizeof(void*)*7 + 3, v_cacheInferType_2632_);
v___x_2635_ = lean_st_ref_take(v_a_2592_);
v_mctx_2636_ = lean_ctor_get(v___x_2635_, 0);
v_cache_2637_ = lean_ctor_get(v___x_2635_, 1);
v_zetaDeltaFVarIds_2638_ = lean_ctor_get(v___x_2635_, 2);
v_postponed_2639_ = lean_ctor_get(v___x_2635_, 3);
v_diag_2640_ = lean_ctor_get(v___x_2635_, 4);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2642_ = v___x_2635_;
v_isShared_2643_ = v_isSharedCheck_2679_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_diag_2640_);
lean_inc(v_postponed_2639_);
lean_inc(v_zetaDeltaFVarIds_2638_);
lean_inc(v_cache_2637_);
lean_inc(v_mctx_2636_);
lean_dec(v___x_2635_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2679_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v_a_2645_; lean_object* v___x_2649_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 2, v___x_2596_);
v___x_2649_ = v___x_2642_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_mctx_2636_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_cache_2637_);
lean_ctor_set(v_reuseFailAlloc_2678_, 2, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2678_, 3, v_postponed_2639_);
lean_ctor_set(v_reuseFailAlloc_2678_, 4, v_diag_2640_);
v___x_2649_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2648_;
}
v___jp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = lean_box(0);
v___x_2647_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2592_, v_zetaDeltaFVarIds_2638_, v___x_2646_);
lean_dec_ref(v___x_2647_);
v_a_2600_ = v_a_2645_;
goto v___jp_2599_;
}
v_reusejp_2648_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_st_ref_put(v_a_2592_, v___x_2649_);
v___x_2651_ = l_Lean_Meta_Closure_collectExpr(v_type_2587_, v_a_2589_, v_a_2590_, v___x_2634_, v_a_2592_, v_a_2593_, v_a_2594_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2653_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
v___x_2653_ = l_Lean_Meta_Closure_collectExpr(v_value_2588_, v_a_2589_, v_a_2590_, v___x_2634_, v_a_2592_, v_a_2593_, v_a_2594_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2655_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v___x_2655_ = l_Lean_Meta_Closure_process(v_a_2589_, v_a_2590_, v___x_2634_, v_a_2592_, v_a_2593_, v_a_2594_);
lean_dec_ref_known(v___x_2634_, 7);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2673_; 
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; 
v_unused_2674_ = lean_ctor_get(v___x_2655_, 0);
lean_dec(v_unused_2674_);
v___x_2657_ = v___x_2655_;
v_isShared_2658_ = v_isSharedCheck_2673_;
goto v_resetjp_2656_;
}
else
{
lean_dec(v___x_2655_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2673_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2659_, 0, v_a_2652_);
lean_ctor_set(v___x_2659_, 1, v_a_2654_);
lean_inc_ref(v___x_2659_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set_tag(v___x_2657_, 1);
lean_ctor_set(v___x_2657_, 0, v___x_2659_);
v___x_2661_ = v___x_2657_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
v___x_2662_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2592_, v_zetaDeltaFVarIds_2638_, v___x_2661_);
lean_dec_ref(v___x_2662_);
v___x_2663_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2592_, v_cache_2598_, v___x_2661_);
lean_dec_ref(v___x_2661_);
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
lean_ctor_set(v___x_2665_, 0, v___x_2659_);
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2659_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
else
{
lean_object* v_a_2675_; 
lean_dec(v_a_2654_);
lean_dec(v_a_2652_);
v_a_2675_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2655_, 1);
v_a_2645_ = v_a_2675_;
goto v___jp_2644_;
}
}
else
{
lean_object* v_a_2676_; 
lean_dec(v_a_2652_);
lean_dec_ref_known(v___x_2634_, 7);
v_a_2676_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2653_, 1);
v_a_2645_ = v_a_2676_;
goto v___jp_2644_;
}
}
else
{
lean_object* v_a_2677_; 
lean_dec_ref_known(v___x_2634_, 7);
lean_dec_ref(v_value_2588_);
v_a_2677_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2651_, 1);
v_a_2645_ = v_a_2677_;
goto v___jp_2644_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* v_type_2683_, lean_object* v_value_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_2683_, v_value_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
return v_res_2692_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_instMonadEIO___redArg();
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object* v_msg_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v_toApplicative_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2744_; 
v___x_2701_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0);
v___x_2702_ = l_StateRefT_x27_instMonad___redArg(v___x_2701_);
v_toApplicative_2703_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; 
v_unused_2745_ = lean_ctor_get(v___x_2702_, 1);
lean_dec(v_unused_2745_);
v___x_2705_ = v___x_2702_;
v_isShared_2706_ = v_isSharedCheck_2744_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_toApplicative_2703_);
lean_dec(v___x_2702_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2744_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v_toFunctor_2707_; lean_object* v_toSeq_2708_; lean_object* v_toSeqLeft_2709_; lean_object* v_toSeqRight_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2742_; 
v_toFunctor_2707_ = lean_ctor_get(v_toApplicative_2703_, 0);
v_toSeq_2708_ = lean_ctor_get(v_toApplicative_2703_, 2);
v_toSeqLeft_2709_ = lean_ctor_get(v_toApplicative_2703_, 3);
v_toSeqRight_2710_ = lean_ctor_get(v_toApplicative_2703_, 4);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_toApplicative_2703_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; 
v_unused_2743_ = lean_ctor_get(v_toApplicative_2703_, 1);
lean_dec(v_unused_2743_);
v___x_2712_ = v_toApplicative_2703_;
v_isShared_2713_ = v_isSharedCheck_2742_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_toSeqRight_2710_);
lean_inc(v_toSeqLeft_2709_);
lean_inc(v_toSeq_2708_);
lean_inc(v_toFunctor_2707_);
lean_dec(v_toApplicative_2703_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2742_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___f_2714_; lean_object* v___f_2715_; lean_object* v___f_2716_; lean_object* v___f_2717_; lean_object* v___x_2718_; lean_object* v___f_2719_; lean_object* v___f_2720_; lean_object* v___f_2721_; lean_object* v___x_2723_; 
v___f_2714_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1));
v___f_2715_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2));
lean_inc_ref(v_toFunctor_2707_);
v___f_2716_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2716_, 0, v_toFunctor_2707_);
v___f_2717_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2717_, 0, v_toFunctor_2707_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___f_2716_);
lean_ctor_set(v___x_2718_, 1, v___f_2717_);
v___f_2719_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2719_, 0, v_toSeqRight_2710_);
v___f_2720_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2720_, 0, v_toSeqLeft_2709_);
v___f_2721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2721_, 0, v_toSeq_2708_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 4, v___f_2719_);
lean_ctor_set(v___x_2712_, 3, v___f_2720_);
lean_ctor_set(v___x_2712_, 2, v___f_2721_);
lean_ctor_set(v___x_2712_, 1, v___f_2714_);
lean_ctor_set(v___x_2712_, 0, v___x_2718_);
v___x_2723_ = v___x_2712_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___f_2714_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v___f_2721_);
lean_ctor_set(v_reuseFailAlloc_2741_, 3, v___f_2720_);
lean_ctor_set(v_reuseFailAlloc_2741_, 4, v___f_2719_);
v___x_2723_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2725_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 1, v___f_2715_);
lean_ctor_set(v___x_2705_, 0, v___x_2723_);
v___x_2725_ = v___x_2705_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2723_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___f_2715_);
v___x_2725_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
lean_object* v___f_2726_; lean_object* v___f_2727_; lean_object* v___f_2728_; lean_object* v___f_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_12483__overap_2738_; lean_object* v___x_2739_; 
lean_inc_ref_n(v___x_2725_, 6);
v___f_2726_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2726_, 0, v___x_2725_);
v___f_2727_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2727_, 0, v___x_2725_);
v___f_2728_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2728_, 0, v___x_2725_);
v___f_2729_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2729_, 0, v___x_2725_);
v___x_2730_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2730_, 0, lean_box(0));
lean_closure_set(v___x_2730_, 1, lean_box(0));
lean_closure_set(v___x_2730_, 2, v___x_2725_);
v___x_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
lean_ctor_set(v___x_2731_, 1, v___f_2726_);
v___x_2732_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2732_, 0, lean_box(0));
lean_closure_set(v___x_2732_, 1, lean_box(0));
lean_closure_set(v___x_2732_, 2, v___x_2725_);
v___x_2733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2731_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
lean_ctor_set(v___x_2733_, 2, v___f_2727_);
lean_ctor_set(v___x_2733_, 3, v___f_2728_);
lean_ctor_set(v___x_2733_, 4, v___f_2729_);
v___x_2734_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2734_, 0, lean_box(0));
lean_closure_set(v___x_2734_, 1, lean_box(0));
lean_closure_set(v___x_2734_, 2, v___x_2725_);
v___x_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v___x_2736_ = lean_box(0);
v___x_2737_ = l_instInhabitedOfMonad___redArg(v___x_2735_, v___x_2736_);
v___x_12483__overap_2738_ = lean_panic_fn_borrowed(v___x_2737_, v_msg_2696_);
lean_dec(v___x_2737_);
lean_inc(v___y_2699_);
lean_inc_ref(v___y_2698_);
v___x_2739_ = lean_apply_4(v___x_12483__overap_2738_, v___y_2697_, v___y_2698_, v___y_2699_, lean_box(0));
return v___x_2739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object* v_msg_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_msg_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
return v_res_2751_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(lean_object* v_a_2752_, lean_object* v_x_2753_){
_start:
{
if (lean_obj_tag(v_x_2753_) == 0)
{
uint8_t v___x_2754_; 
v___x_2754_ = 0;
return v___x_2754_;
}
else
{
lean_object* v_key_2755_; lean_object* v_tail_2756_; uint8_t v___x_2757_; 
v_key_2755_ = lean_ctor_get(v_x_2753_, 0);
v_tail_2756_ = lean_ctor_get(v_x_2753_, 2);
v___x_2757_ = l_Lean_instBEqFVarId_beq(v_key_2755_, v_a_2752_);
if (v___x_2757_ == 0)
{
v_x_2753_ = v_tail_2756_;
goto _start;
}
else
{
return v___x_2757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg___boxed(lean_object* v_a_2759_, lean_object* v_x_2760_){
_start:
{
uint8_t v_res_2761_; lean_object* v_r_2762_; 
v_res_2761_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2759_, v_x_2760_);
lean_dec(v_x_2760_);
lean_dec(v_a_2759_);
v_r_2762_ = lean_box(v_res_2761_);
return v_r_2762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(lean_object* v_x_2763_, lean_object* v_x_2764_){
_start:
{
if (lean_obj_tag(v_x_2764_) == 0)
{
return v_x_2763_;
}
else
{
lean_object* v_key_2765_; lean_object* v_value_2766_; lean_object* v_tail_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2790_; 
v_key_2765_ = lean_ctor_get(v_x_2764_, 0);
v_value_2766_ = lean_ctor_get(v_x_2764_, 1);
v_tail_2767_ = lean_ctor_get(v_x_2764_, 2);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_x_2764_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2769_ = v_x_2764_;
v_isShared_2770_ = v_isSharedCheck_2790_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_tail_2767_);
lean_inc(v_value_2766_);
lean_inc(v_key_2765_);
lean_dec(v_x_2764_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2790_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; uint64_t v___x_2772_; uint64_t v___x_2773_; uint64_t v___x_2774_; uint64_t v_fold_2775_; uint64_t v___x_2776_; uint64_t v___x_2777_; uint64_t v___x_2778_; size_t v___x_2779_; size_t v___x_2780_; size_t v___x_2781_; size_t v___x_2782_; size_t v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2771_ = lean_array_get_size(v_x_2763_);
v___x_2772_ = l_Lean_instHashableFVarId_hash(v_key_2765_);
v___x_2773_ = 32ULL;
v___x_2774_ = lean_uint64_shift_right(v___x_2772_, v___x_2773_);
v_fold_2775_ = lean_uint64_xor(v___x_2772_, v___x_2774_);
v___x_2776_ = 16ULL;
v___x_2777_ = lean_uint64_shift_right(v_fold_2775_, v___x_2776_);
v___x_2778_ = lean_uint64_xor(v_fold_2775_, v___x_2777_);
v___x_2779_ = lean_uint64_to_usize(v___x_2778_);
v___x_2780_ = lean_usize_of_nat(v___x_2771_);
v___x_2781_ = ((size_t)1ULL);
v___x_2782_ = lean_usize_sub(v___x_2780_, v___x_2781_);
v___x_2783_ = lean_usize_land(v___x_2779_, v___x_2782_);
v___x_2784_ = lean_array_uget_borrowed(v_x_2763_, v___x_2783_);
lean_inc(v___x_2784_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 2, v___x_2784_);
v___x_2786_ = v___x_2769_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_key_2765_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_value_2766_);
lean_ctor_set(v_reuseFailAlloc_2789_, 2, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_array_uset(v_x_2763_, v___x_2783_, v___x_2786_);
v_x_2763_ = v___x_2787_;
v_x_2764_ = v_tail_2767_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(lean_object* v_i_2791_, lean_object* v_source_2792_, lean_object* v_target_2793_){
_start:
{
lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2794_ = lean_array_get_size(v_source_2792_);
v___x_2795_ = lean_nat_dec_lt(v_i_2791_, v___x_2794_);
if (v___x_2795_ == 0)
{
lean_dec_ref(v_source_2792_);
lean_dec(v_i_2791_);
return v_target_2793_;
}
else
{
lean_object* v_es_2796_; lean_object* v___x_2797_; lean_object* v_source_2798_; lean_object* v_target_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v_es_2796_ = lean_array_fget(v_source_2792_, v_i_2791_);
v___x_2797_ = lean_box(0);
v_source_2798_ = lean_array_fset(v_source_2792_, v_i_2791_, v___x_2797_);
v_target_2799_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_target_2793_, v_es_2796_);
v___x_2800_ = lean_unsigned_to_nat(1u);
v___x_2801_ = lean_nat_add(v_i_2791_, v___x_2800_);
lean_dec(v_i_2791_);
v_i_2791_ = v___x_2801_;
v_source_2792_ = v_source_2798_;
v_target_2793_ = v_target_2799_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(lean_object* v_data_2803_){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v_nbuckets_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2804_ = lean_array_get_size(v_data_2803_);
v___x_2805_ = lean_unsigned_to_nat(2u);
v_nbuckets_2806_ = lean_nat_mul(v___x_2804_, v___x_2805_);
v___x_2807_ = lean_unsigned_to_nat(0u);
v___x_2808_ = lean_box(0);
v___x_2809_ = lean_mk_array(v_nbuckets_2806_, v___x_2808_);
v___x_2810_ = lean_array_propagate_mark(v_data_2803_, v___x_2809_);
v___x_2811_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v___x_2807_, v_data_2803_, v___x_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(lean_object* v_m_2812_, lean_object* v_a_2813_, lean_object* v_b_2814_){
_start:
{
lean_object* v_size_2815_; lean_object* v_buckets_2816_; lean_object* v___x_2817_; uint64_t v___x_2818_; uint64_t v___x_2819_; uint64_t v___x_2820_; uint64_t v_fold_2821_; uint64_t v___x_2822_; uint64_t v___x_2823_; uint64_t v___x_2824_; size_t v___x_2825_; size_t v___x_2826_; size_t v___x_2827_; size_t v___x_2828_; size_t v___x_2829_; lean_object* v_bkt_2830_; uint8_t v___x_2831_; 
v_size_2815_ = lean_ctor_get(v_m_2812_, 0);
v_buckets_2816_ = lean_ctor_get(v_m_2812_, 1);
v___x_2817_ = lean_array_get_size(v_buckets_2816_);
v___x_2818_ = l_Lean_instHashableFVarId_hash(v_a_2813_);
v___x_2819_ = 32ULL;
v___x_2820_ = lean_uint64_shift_right(v___x_2818_, v___x_2819_);
v_fold_2821_ = lean_uint64_xor(v___x_2818_, v___x_2820_);
v___x_2822_ = 16ULL;
v___x_2823_ = lean_uint64_shift_right(v_fold_2821_, v___x_2822_);
v___x_2824_ = lean_uint64_xor(v_fold_2821_, v___x_2823_);
v___x_2825_ = lean_uint64_to_usize(v___x_2824_);
v___x_2826_ = lean_usize_of_nat(v___x_2817_);
v___x_2827_ = ((size_t)1ULL);
v___x_2828_ = lean_usize_sub(v___x_2826_, v___x_2827_);
v___x_2829_ = lean_usize_land(v___x_2825_, v___x_2828_);
v_bkt_2830_ = lean_array_uget_borrowed(v_buckets_2816_, v___x_2829_);
v___x_2831_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2813_, v_bkt_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2852_; 
lean_inc_ref(v_buckets_2816_);
lean_inc(v_size_2815_);
v_isSharedCheck_2852_ = !lean_is_exclusive(v_m_2812_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; lean_object* v_unused_2854_; 
v_unused_2853_ = lean_ctor_get(v_m_2812_, 1);
lean_dec(v_unused_2853_);
v_unused_2854_ = lean_ctor_get(v_m_2812_, 0);
lean_dec(v_unused_2854_);
v___x_2833_ = v_m_2812_;
v_isShared_2834_ = v_isSharedCheck_2852_;
goto v_resetjp_2832_;
}
else
{
lean_dec(v_m_2812_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2852_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v_size_x27_2836_; lean_object* v___x_2837_; lean_object* v_buckets_x27_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2835_ = lean_unsigned_to_nat(1u);
v_size_x27_2836_ = lean_nat_add(v_size_2815_, v___x_2835_);
lean_dec(v_size_2815_);
lean_inc(v_bkt_2830_);
v___x_2837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2837_, 0, v_a_2813_);
lean_ctor_set(v___x_2837_, 1, v_b_2814_);
lean_ctor_set(v___x_2837_, 2, v_bkt_2830_);
v_buckets_x27_2838_ = lean_array_uset(v_buckets_2816_, v___x_2829_, v___x_2837_);
v___x_2839_ = lean_unsigned_to_nat(4u);
v___x_2840_ = lean_nat_mul(v_size_x27_2836_, v___x_2839_);
v___x_2841_ = lean_unsigned_to_nat(3u);
v___x_2842_ = lean_nat_div(v___x_2840_, v___x_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_array_get_size(v_buckets_x27_2838_);
v___x_2844_ = lean_nat_dec_le(v___x_2842_, v___x_2843_);
lean_dec(v___x_2842_);
if (v___x_2844_ == 0)
{
lean_object* v_val_2845_; lean_object* v___x_2847_; 
v_val_2845_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_2838_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 1, v_val_2845_);
lean_ctor_set(v___x_2833_, 0, v_size_x27_2836_);
v___x_2847_ = v___x_2833_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_size_x27_2836_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_val_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
else
{
lean_object* v___x_2850_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 1, v_buckets_x27_2838_);
lean_ctor_set(v___x_2833_, 0, v_size_x27_2836_);
v___x_2850_ = v___x_2833_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_size_x27_2836_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_buckets_x27_2838_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
else
{
lean_dec(v_b_2814_);
lean_dec(v_a_2813_);
return v_m_2812_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object* v_m_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_buckets_2857_; lean_object* v___x_2858_; uint64_t v___x_2859_; uint64_t v___x_2860_; uint64_t v___x_2861_; uint64_t v_fold_2862_; uint64_t v___x_2863_; uint64_t v___x_2864_; uint64_t v___x_2865_; size_t v___x_2866_; size_t v___x_2867_; size_t v___x_2868_; size_t v___x_2869_; size_t v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v_buckets_2857_ = lean_ctor_get(v_m_2855_, 1);
v___x_2858_ = lean_array_get_size(v_buckets_2857_);
v___x_2859_ = l_Lean_instHashableFVarId_hash(v_a_2856_);
v___x_2860_ = 32ULL;
v___x_2861_ = lean_uint64_shift_right(v___x_2859_, v___x_2860_);
v_fold_2862_ = lean_uint64_xor(v___x_2859_, v___x_2861_);
v___x_2863_ = 16ULL;
v___x_2864_ = lean_uint64_shift_right(v_fold_2862_, v___x_2863_);
v___x_2865_ = lean_uint64_xor(v_fold_2862_, v___x_2864_);
v___x_2866_ = lean_uint64_to_usize(v___x_2865_);
v___x_2867_ = lean_usize_of_nat(v___x_2858_);
v___x_2868_ = ((size_t)1ULL);
v___x_2869_ = lean_usize_sub(v___x_2867_, v___x_2868_);
v___x_2870_ = lean_usize_land(v___x_2866_, v___x_2869_);
v___x_2871_ = lean_array_uget_borrowed(v_buckets_2857_, v___x_2870_);
v___x_2872_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2856_, v___x_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object* v_m_2873_, lean_object* v_a_2874_){
_start:
{
uint8_t v_res_2875_; lean_object* v_r_2876_; 
v_res_2875_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_2873_, v_a_2874_);
lean_dec(v_a_2874_);
lean_dec_ref(v_m_2873_);
v_r_2876_ = lean_box(v_res_2875_);
return v_r_2876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(lean_object* v_a_2877_, lean_object* v_x_2878_){
_start:
{
if (lean_obj_tag(v_x_2878_) == 0)
{
lean_object* v___x_2879_; 
v___x_2879_ = lean_box(0);
return v___x_2879_;
}
else
{
lean_object* v_key_2880_; lean_object* v_value_2881_; lean_object* v_tail_2882_; uint8_t v___x_2883_; 
v_key_2880_ = lean_ctor_get(v_x_2878_, 0);
v_value_2881_ = lean_ctor_get(v_x_2878_, 1);
v_tail_2882_ = lean_ctor_get(v_x_2878_, 2);
v___x_2883_ = lean_expr_eqv(v_key_2880_, v_a_2877_);
if (v___x_2883_ == 0)
{
v_x_2878_ = v_tail_2882_;
goto _start;
}
else
{
lean_object* v___x_2885_; 
lean_inc(v_value_2881_);
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_value_2881_);
return v___x_2885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_a_2886_, lean_object* v_x_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2886_, v_x_2887_);
lean_dec(v_x_2887_);
lean_dec_ref(v_a_2886_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(lean_object* v_m_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v_buckets_2891_; lean_object* v___x_2892_; uint64_t v___x_2893_; uint64_t v___x_2894_; uint64_t v___x_2895_; uint64_t v_fold_2896_; uint64_t v___x_2897_; uint64_t v___x_2898_; uint64_t v___x_2899_; size_t v___x_2900_; size_t v___x_2901_; size_t v___x_2902_; size_t v___x_2903_; size_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_buckets_2891_ = lean_ctor_get(v_m_2889_, 1);
v___x_2892_ = lean_array_get_size(v_buckets_2891_);
v___x_2893_ = l_Lean_Expr_hash(v_a_2890_);
v___x_2894_ = 32ULL;
v___x_2895_ = lean_uint64_shift_right(v___x_2893_, v___x_2894_);
v_fold_2896_ = lean_uint64_xor(v___x_2893_, v___x_2895_);
v___x_2897_ = 16ULL;
v___x_2898_ = lean_uint64_shift_right(v_fold_2896_, v___x_2897_);
v___x_2899_ = lean_uint64_xor(v_fold_2896_, v___x_2898_);
v___x_2900_ = lean_uint64_to_usize(v___x_2899_);
v___x_2901_ = lean_usize_of_nat(v___x_2892_);
v___x_2902_ = ((size_t)1ULL);
v___x_2903_ = lean_usize_sub(v___x_2901_, v___x_2902_);
v___x_2904_ = lean_usize_land(v___x_2900_, v___x_2903_);
v___x_2905_ = lean_array_uget_borrowed(v_buckets_2891_, v___x_2904_);
v___x_2906_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2890_, v___x_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg___boxed(lean_object* v_m_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_2907_, v_a_2908_);
lean_dec_ref(v_a_2908_);
lean_dec_ref(v_m_2907_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(lean_object* v_a_2910_, lean_object* v_b_2911_, lean_object* v_x_2912_){
_start:
{
if (lean_obj_tag(v_x_2912_) == 0)
{
lean_dec(v_b_2911_);
lean_dec_ref(v_a_2910_);
return v_x_2912_;
}
else
{
lean_object* v_key_2913_; lean_object* v_value_2914_; lean_object* v_tail_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2927_; 
v_key_2913_ = lean_ctor_get(v_x_2912_, 0);
v_value_2914_ = lean_ctor_get(v_x_2912_, 1);
v_tail_2915_ = lean_ctor_get(v_x_2912_, 2);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_x_2912_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2917_ = v_x_2912_;
v_isShared_2918_ = v_isSharedCheck_2927_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_tail_2915_);
lean_inc(v_value_2914_);
lean_inc(v_key_2913_);
lean_dec(v_x_2912_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2927_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
uint8_t v___x_2919_; 
v___x_2919_ = lean_expr_eqv(v_key_2913_, v_a_2910_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2920_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_2910_, v_b_2911_, v_tail_2915_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 2, v___x_2920_);
v___x_2922_ = v___x_2917_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_key_2913_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_value_2914_);
lean_ctor_set(v_reuseFailAlloc_2923_, 2, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
else
{
lean_object* v___x_2925_; 
lean_dec(v_value_2914_);
lean_dec(v_key_2913_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 1, v_b_2911_);
lean_ctor_set(v___x_2917_, 0, v_a_2910_);
v___x_2925_ = v___x_2917_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2910_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_b_2911_);
lean_ctor_set(v_reuseFailAlloc_2926_, 2, v_tail_2915_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(lean_object* v_x_2928_, lean_object* v_x_2929_){
_start:
{
if (lean_obj_tag(v_x_2929_) == 0)
{
return v_x_2928_;
}
else
{
lean_object* v_key_2930_; lean_object* v_value_2931_; lean_object* v_tail_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2955_; 
v_key_2930_ = lean_ctor_get(v_x_2929_, 0);
v_value_2931_ = lean_ctor_get(v_x_2929_, 1);
v_tail_2932_ = lean_ctor_get(v_x_2929_, 2);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_x_2929_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2934_ = v_x_2929_;
v_isShared_2935_ = v_isSharedCheck_2955_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_tail_2932_);
lean_inc(v_value_2931_);
lean_inc(v_key_2930_);
lean_dec(v_x_2929_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2955_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; uint64_t v___x_2937_; uint64_t v___x_2938_; uint64_t v___x_2939_; uint64_t v_fold_2940_; uint64_t v___x_2941_; uint64_t v___x_2942_; uint64_t v___x_2943_; size_t v___x_2944_; size_t v___x_2945_; size_t v___x_2946_; size_t v___x_2947_; size_t v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2936_ = lean_array_get_size(v_x_2928_);
v___x_2937_ = l_Lean_Expr_hash(v_key_2930_);
v___x_2938_ = 32ULL;
v___x_2939_ = lean_uint64_shift_right(v___x_2937_, v___x_2938_);
v_fold_2940_ = lean_uint64_xor(v___x_2937_, v___x_2939_);
v___x_2941_ = 16ULL;
v___x_2942_ = lean_uint64_shift_right(v_fold_2940_, v___x_2941_);
v___x_2943_ = lean_uint64_xor(v_fold_2940_, v___x_2942_);
v___x_2944_ = lean_uint64_to_usize(v___x_2943_);
v___x_2945_ = lean_usize_of_nat(v___x_2936_);
v___x_2946_ = ((size_t)1ULL);
v___x_2947_ = lean_usize_sub(v___x_2945_, v___x_2946_);
v___x_2948_ = lean_usize_land(v___x_2944_, v___x_2947_);
v___x_2949_ = lean_array_uget_borrowed(v_x_2928_, v___x_2948_);
lean_inc(v___x_2949_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 2, v___x_2949_);
v___x_2951_ = v___x_2934_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_key_2930_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_value_2931_);
lean_ctor_set(v_reuseFailAlloc_2954_, 2, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_array_uset(v_x_2928_, v___x_2948_, v___x_2951_);
v_x_2928_ = v___x_2952_;
v_x_2929_ = v_tail_2932_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(lean_object* v_i_2956_, lean_object* v_source_2957_, lean_object* v_target_2958_){
_start:
{
lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2959_ = lean_array_get_size(v_source_2957_);
v___x_2960_ = lean_nat_dec_lt(v_i_2956_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_dec_ref(v_source_2957_);
lean_dec(v_i_2956_);
return v_target_2958_;
}
else
{
lean_object* v_es_2961_; lean_object* v___x_2962_; lean_object* v_source_2963_; lean_object* v_target_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_es_2961_ = lean_array_fget(v_source_2957_, v_i_2956_);
v___x_2962_ = lean_box(0);
v_source_2963_ = lean_array_fset(v_source_2957_, v_i_2956_, v___x_2962_);
v_target_2964_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_target_2958_, v_es_2961_);
v___x_2965_ = lean_unsigned_to_nat(1u);
v___x_2966_ = lean_nat_add(v_i_2956_, v___x_2965_);
lean_dec(v_i_2956_);
v_i_2956_ = v___x_2966_;
v_source_2957_ = v_source_2963_;
v_target_2958_ = v_target_2964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(lean_object* v_data_2968_){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v_nbuckets_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2969_ = lean_array_get_size(v_data_2968_);
v___x_2970_ = lean_unsigned_to_nat(2u);
v_nbuckets_2971_ = lean_nat_mul(v___x_2969_, v___x_2970_);
v___x_2972_ = lean_unsigned_to_nat(0u);
v___x_2973_ = lean_box(0);
v___x_2974_ = lean_mk_array(v_nbuckets_2971_, v___x_2973_);
v___x_2975_ = lean_array_propagate_mark(v_data_2968_, v___x_2974_);
v___x_2976_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v___x_2972_, v_data_2968_, v___x_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(lean_object* v_a_2977_, lean_object* v_x_2978_){
_start:
{
if (lean_obj_tag(v_x_2978_) == 0)
{
uint8_t v___x_2979_; 
v___x_2979_ = 0;
return v___x_2979_;
}
else
{
lean_object* v_key_2980_; lean_object* v_tail_2981_; uint8_t v___x_2982_; 
v_key_2980_ = lean_ctor_get(v_x_2978_, 0);
v_tail_2981_ = lean_ctor_get(v_x_2978_, 2);
v___x_2982_ = lean_expr_eqv(v_key_2980_, v_a_2977_);
if (v___x_2982_ == 0)
{
v_x_2978_ = v_tail_2981_;
goto _start;
}
else
{
return v___x_2982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_2984_, lean_object* v_x_2985_){
_start:
{
uint8_t v_res_2986_; lean_object* v_r_2987_; 
v_res_2986_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_2984_, v_x_2985_);
lean_dec(v_x_2985_);
lean_dec_ref(v_a_2984_);
v_r_2987_ = lean_box(v_res_2986_);
return v_r_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(lean_object* v_m_2988_, lean_object* v_a_2989_, lean_object* v_b_2990_){
_start:
{
lean_object* v_size_2991_; lean_object* v_buckets_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3035_; 
v_size_2991_ = lean_ctor_get(v_m_2988_, 0);
v_buckets_2992_ = lean_ctor_get(v_m_2988_, 1);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_m_2988_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_2994_ = v_m_2988_;
v_isShared_2995_ = v_isSharedCheck_3035_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_buckets_2992_);
lean_inc(v_size_2991_);
lean_dec(v_m_2988_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3035_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; uint64_t v___x_2997_; uint64_t v___x_2998_; uint64_t v___x_2999_; uint64_t v_fold_3000_; uint64_t v___x_3001_; uint64_t v___x_3002_; uint64_t v___x_3003_; size_t v___x_3004_; size_t v___x_3005_; size_t v___x_3006_; size_t v___x_3007_; size_t v___x_3008_; lean_object* v_bkt_3009_; uint8_t v___x_3010_; 
v___x_2996_ = lean_array_get_size(v_buckets_2992_);
v___x_2997_ = l_Lean_Expr_hash(v_a_2989_);
v___x_2998_ = 32ULL;
v___x_2999_ = lean_uint64_shift_right(v___x_2997_, v___x_2998_);
v_fold_3000_ = lean_uint64_xor(v___x_2997_, v___x_2999_);
v___x_3001_ = 16ULL;
v___x_3002_ = lean_uint64_shift_right(v_fold_3000_, v___x_3001_);
v___x_3003_ = lean_uint64_xor(v_fold_3000_, v___x_3002_);
v___x_3004_ = lean_uint64_to_usize(v___x_3003_);
v___x_3005_ = lean_usize_of_nat(v___x_2996_);
v___x_3006_ = ((size_t)1ULL);
v___x_3007_ = lean_usize_sub(v___x_3005_, v___x_3006_);
v___x_3008_ = lean_usize_land(v___x_3004_, v___x_3007_);
v_bkt_3009_ = lean_array_uget_borrowed(v_buckets_2992_, v___x_3008_);
v___x_3010_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_2989_, v_bkt_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v_size_x27_3012_; lean_object* v___x_3013_; lean_object* v_buckets_x27_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3011_ = lean_unsigned_to_nat(1u);
v_size_x27_3012_ = lean_nat_add(v_size_2991_, v___x_3011_);
lean_dec(v_size_2991_);
lean_inc(v_bkt_3009_);
v___x_3013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3013_, 0, v_a_2989_);
lean_ctor_set(v___x_3013_, 1, v_b_2990_);
lean_ctor_set(v___x_3013_, 2, v_bkt_3009_);
v_buckets_x27_3014_ = lean_array_uset(v_buckets_2992_, v___x_3008_, v___x_3013_);
v___x_3015_ = lean_unsigned_to_nat(4u);
v___x_3016_ = lean_nat_mul(v_size_x27_3012_, v___x_3015_);
v___x_3017_ = lean_unsigned_to_nat(3u);
v___x_3018_ = lean_nat_div(v___x_3016_, v___x_3017_);
lean_dec(v___x_3016_);
v___x_3019_ = lean_array_get_size(v_buckets_x27_3014_);
v___x_3020_ = lean_nat_dec_le(v___x_3018_, v___x_3019_);
lean_dec(v___x_3018_);
if (v___x_3020_ == 0)
{
lean_object* v_val_3021_; lean_object* v___x_3023_; 
v_val_3021_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_buckets_x27_3014_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 1, v_val_3021_);
lean_ctor_set(v___x_2994_, 0, v_size_x27_3012_);
v___x_3023_ = v___x_2994_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_size_x27_3012_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_val_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
else
{
lean_object* v___x_3026_; 
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 1, v_buckets_x27_3014_);
lean_ctor_set(v___x_2994_, 0, v_size_x27_3012_);
v___x_3026_ = v___x_2994_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_size_x27_3012_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_buckets_x27_3014_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
else
{
lean_object* v___x_3028_; lean_object* v_buckets_x27_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3033_; 
lean_inc(v_bkt_3009_);
v___x_3028_ = lean_box(0);
v_buckets_x27_3029_ = lean_array_uset(v_buckets_2992_, v___x_3008_, v___x_3028_);
v___x_3030_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_2989_, v_b_2990_, v_bkt_3009_);
v___x_3031_ = lean_array_uset(v_buckets_x27_3029_, v___x_3008_, v___x_3030_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 1, v___x_3031_);
v___x_3033_ = v___x_2994_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_size_2991_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v___x_3031_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object* v_g_3036_, lean_object* v_e_3037_, lean_object* v_a_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_a_3044_; lean_object* v_fst_3045_; lean_object* v___y_3051_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_st_ref_get(v_a_3038_);
v___x_3055_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v___x_3054_, v_e_3037_);
lean_dec(v___x_3054_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v___x_3056_; 
lean_inc_ref(v_g_3036_);
lean_inc(v___y_3041_);
lean_inc_ref(v___y_3040_);
lean_inc_ref(v_e_3037_);
v___x_3056_ = lean_apply_5(v_g_3036_, v_e_3037_, v___y_3039_, v___y_3040_, v___y_3041_, lean_box(0));
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v_fst_3058_; lean_object* v_snd_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3104_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3056_, 1);
v_fst_3058_ = lean_ctor_get(v_a_3057_, 0);
v_snd_3059_ = lean_ctor_get(v_a_3057_, 1);
v_isSharedCheck_3104_ = !lean_is_exclusive(v_a_3057_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3061_ = v_a_3057_;
v_isShared_3062_ = v_isSharedCheck_3104_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_snd_3059_);
lean_inc(v_fst_3058_);
lean_dec(v_a_3057_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3104_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v_d_3064_; lean_object* v_b_3065_; lean_object* v___y_3066_; uint8_t v___x_3071_; 
v___x_3071_ = lean_unbox(v_fst_3058_);
lean_dec(v_fst_3058_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; lean_object* v___x_3074_; 
lean_dec_ref(v_g_3036_);
v___x_3072_ = lean_box(0);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3072_);
v___x_3074_ = v___x_3061_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_snd_3059_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
v_a_3044_ = v___x_3074_;
v_fst_3045_ = v___x_3072_;
goto v___jp_3043_;
}
}
else
{
switch(lean_obj_tag(v_e_3037_))
{
case 7:
{
lean_object* v_binderType_3076_; lean_object* v_body_3077_; 
lean_del_object(v___x_3061_);
v_binderType_3076_ = lean_ctor_get(v_e_3037_, 1);
v_body_3077_ = lean_ctor_get(v_e_3037_, 2);
lean_inc_ref(v_body_3077_);
lean_inc_ref(v_binderType_3076_);
v_d_3064_ = v_binderType_3076_;
v_b_3065_ = v_body_3077_;
v___y_3066_ = v_a_3038_;
goto v___jp_3063_;
}
case 6:
{
lean_object* v_binderType_3078_; lean_object* v_body_3079_; 
lean_del_object(v___x_3061_);
v_binderType_3078_ = lean_ctor_get(v_e_3037_, 1);
v_body_3079_ = lean_ctor_get(v_e_3037_, 2);
lean_inc_ref(v_body_3079_);
lean_inc_ref(v_binderType_3078_);
v_d_3064_ = v_binderType_3078_;
v_b_3065_ = v_body_3079_;
v___y_3066_ = v_a_3038_;
goto v___jp_3063_;
}
case 8:
{
lean_object* v_type_3080_; lean_object* v_value_3081_; lean_object* v_body_3082_; lean_object* v___x_3083_; 
lean_del_object(v___x_3061_);
v_type_3080_ = lean_ctor_get(v_e_3037_, 1);
v_value_3081_ = lean_ctor_get(v_e_3037_, 2);
v_body_3082_ = lean_ctor_get(v_e_3037_, 3);
lean_inc_ref(v_type_3080_);
lean_inc_ref(v_g_3036_);
v___x_3083_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3036_, v_type_3080_, v_a_3038_, v_snd_3059_, v___y_3040_, v___y_3041_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v_snd_3085_; lean_object* v___x_3086_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
v_snd_3085_ = lean_ctor_get(v_a_3084_, 1);
lean_inc(v_snd_3085_);
lean_dec(v_a_3084_);
lean_inc_ref(v_value_3081_);
lean_inc_ref(v_g_3036_);
v___x_3086_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3036_, v_value_3081_, v_a_3038_, v_snd_3085_, v___y_3040_, v___y_3041_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v_snd_3088_; lean_object* v___x_3089_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3086_, 1);
v_snd_3088_ = lean_ctor_get(v_a_3087_, 1);
lean_inc(v_snd_3088_);
lean_dec(v_a_3087_);
lean_inc_ref(v_body_3082_);
v___x_3089_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3036_, v_body_3082_, v_a_3038_, v_snd_3088_, v___y_3040_, v___y_3041_);
v___y_3051_ = v___x_3089_;
goto v___jp_3050_;
}
else
{
lean_dec_ref_known(v_e_3037_, 4);
lean_dec_ref(v_g_3036_);
return v___x_3086_;
}
}
else
{
lean_dec_ref_known(v_e_3037_, 4);
lean_dec_ref(v_g_3036_);
return v___x_3083_;
}
}
case 5:
{
lean_object* v_fn_3090_; lean_object* v_arg_3091_; lean_object* v___x_3092_; 
lean_del_object(v___x_3061_);
v_fn_3090_ = lean_ctor_get(v_e_3037_, 0);
v_arg_3091_ = lean_ctor_get(v_e_3037_, 1);
lean_inc_ref(v_fn_3090_);
lean_inc_ref(v_g_3036_);
v___x_3092_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3036_, v_fn_3090_, v_a_3038_, v_snd_3059_, v___y_3040_, v___y_3041_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v_snd_3094_; lean_object* v___x_3095_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
lean_dec_ref_known(v___x_3092_, 1);
v_snd_3094_ = lean_ctor_get(v_a_3093_, 1);
lean_inc(v_snd_3094_);
lean_dec(v_a_3093_);
lean_inc_ref(v_arg_3091_);
v___x_3095_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3036_, v_arg_3091_, v_a_3038_, v_snd_3094_, v___y_3040_, v___y_3041_);
v___y_3051_ = v___x_3095_;
goto v___jp_3050_;
}
else
{
lean_dec_ref_known(v_e_3037_, 2);
lean_dec_ref(v_g_3036_);
return v___x_3092_;
}
}
case 10:
{
lean_object* v_expr_3096_; lean_object* v___x_3097_; 
lean_del_object(v___x_3061_);
v_expr_3096_ = lean_ctor_get(v_e_3037_, 1);
lean_inc_ref(v_expr_3096_);
v___x_3097_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3036_, v_expr_3096_, v_a_3038_, v_snd_3059_, v___y_3040_, v___y_3041_);
v___y_3051_ = v___x_3097_;
goto v___jp_3050_;
}
case 11:
{
lean_object* v_struct_3098_; lean_object* v___x_3099_; 
lean_del_object(v___x_3061_);
v_struct_3098_ = lean_ctor_get(v_e_3037_, 2);
lean_inc_ref(v_struct_3098_);
v___x_3099_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3036_, v_struct_3098_, v_a_3038_, v_snd_3059_, v___y_3040_, v___y_3041_);
v___y_3051_ = v___x_3099_;
goto v___jp_3050_;
}
default: 
{
lean_object* v___x_3100_; lean_object* v___x_3102_; 
lean_dec_ref(v_g_3036_);
v___x_3100_ = lean_box(0);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3100_);
v___x_3102_ = v___x_3061_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_snd_3059_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
v_a_3044_ = v___x_3102_;
v_fst_3045_ = v___x_3100_;
goto v___jp_3043_;
}
}
}
}
v___jp_3063_:
{
lean_object* v___x_3067_; 
lean_inc_ref(v_g_3036_);
v___x_3067_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3036_, v_d_3064_, v___y_3066_, v_snd_3059_, v___y_3040_, v___y_3041_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v_snd_3069_; lean_object* v___x_3070_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v_snd_3069_ = lean_ctor_get(v_a_3068_, 1);
lean_inc(v_snd_3069_);
lean_dec(v_a_3068_);
v___x_3070_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3036_, v_b_3065_, v___y_3066_, v_snd_3069_, v___y_3040_, v___y_3041_);
v___y_3051_ = v___x_3070_;
goto v___jp_3050_;
}
else
{
lean_dec_ref(v_b_3065_);
lean_dec_ref(v_e_3037_);
lean_dec_ref(v_g_3036_);
return v___x_3067_;
}
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec_ref(v_e_3037_);
lean_dec_ref(v_g_3036_);
v_a_3105_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3056_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3056_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_val_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3121_; 
lean_dec_ref(v_e_3037_);
lean_dec_ref(v_g_3036_);
v_val_3113_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3115_ = v___x_3055_;
v_isShared_3116_ = v_isSharedCheck_3121_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_val_3113_);
lean_dec(v___x_3055_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3121_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3117_, 0, v_val_3113_);
lean_ctor_set(v___x_3117_, 1, v___y_3039_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set_tag(v___x_3115_, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3117_);
v___x_3119_ = v___x_3115_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3117_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
v___jp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3046_ = lean_st_ref_take(v_a_3038_);
v___x_3047_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v___x_3046_, v_e_3037_, v_fst_3045_);
v___x_3048_ = lean_st_ref_put(v_a_3038_, v___x_3047_);
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_a_3044_);
return v___x_3049_;
}
v___jp_3050_:
{
if (lean_obj_tag(v___y_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v_fst_3053_; 
v_a_3052_ = lean_ctor_get(v___y_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref_known(v___y_3051_, 1);
v_fst_3053_ = lean_ctor_get(v_a_3052_, 0);
lean_inc(v_fst_3053_);
v_a_3044_ = v_a_3052_;
v_fst_3045_ = v_fst_3053_;
goto v___jp_3043_;
}
else
{
lean_dec_ref(v_e_3037_);
return v___y_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___boxed(lean_object* v_g_3122_, lean_object* v_e_3123_, lean_object* v_a_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3122_, v_e_3123_, v_a_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v_a_3124_);
return v_res_3129_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
return v___x_3131_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3132_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3133_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3134_ = lean_unsigned_to_nat(0u);
v___x_3135_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
lean_ctor_set(v___x_3135_, 2, v___x_3134_);
lean_ctor_set(v___x_3135_, 3, v___x_3134_);
lean_ctor_set(v___x_3135_, 4, v___x_3133_);
lean_ctor_set(v___x_3135_, 5, v___x_3133_);
lean_ctor_set(v___x_3135_, 6, v___x_3133_);
lean_ctor_set(v___x_3135_, 7, v___x_3133_);
lean_ctor_set(v___x_3135_, 8, v___x_3133_);
lean_ctor_set(v___x_3135_, 9, v___x_3133_);
lean_ctor_set(v___x_3135_, 10, v___x_3133_);
lean_ctor_set(v___x_3135_, 11, v___x_3132_);
return v___x_3135_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = lean_unsigned_to_nat(32u);
v___x_3137_ = lean_mk_empty_array_with_capacity(v___x_3136_);
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3(void){
_start:
{
size_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3139_ = ((size_t)5ULL);
v___x_3140_ = lean_unsigned_to_nat(0u);
v___x_3141_ = lean_unsigned_to_nat(32u);
v___x_3142_ = lean_mk_empty_array_with_capacity(v___x_3141_);
v___x_3143_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2);
v___x_3144_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
lean_ctor_set(v___x_3144_, 1, v___x_3142_);
lean_ctor_set(v___x_3144_, 2, v___x_3140_);
lean_ctor_set(v___x_3144_, 3, v___x_3140_);
lean_ctor_set_usize(v___x_3144_, 4, v___x_3139_);
return v___x_3144_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3145_ = lean_box(1);
v___x_3146_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3);
v___x_3147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
lean_ctor_set(v___x_3148_, 1, v___x_3146_);
lean_ctor_set(v___x_3148_, 2, v___x_3145_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(lean_object* v_msgData_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v___x_3153_; lean_object* v_toCold_3154_; lean_object* v_env_3155_; lean_object* v_options_3156_; uint8_t v___x_3157_; lean_object* v_env_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3153_ = lean_st_ref_get(v___y_3151_);
v_toCold_3154_ = lean_ctor_get(v___y_3150_, 0);
v_env_3155_ = lean_ctor_get(v___x_3153_, 0);
lean_inc_ref(v_env_3155_);
lean_dec(v___x_3153_);
v_options_3156_ = lean_ctor_get(v_toCold_3154_, 2);
v___x_3157_ = 0;
v_env_3158_ = l_Lean_Environment_setRecordingDeps(v_env_3155_, v___x_3157_);
v___x_3159_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3160_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4);
lean_inc_ref(v_options_3156_);
v___x_3161_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3161_, 0, v_env_3158_);
lean_ctor_set(v___x_3161_, 1, v___x_3159_);
lean_ctor_set(v___x_3161_, 2, v___x_3160_);
lean_ctor_set(v___x_3161_, 3, v_options_3156_);
v___x_3162_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
lean_ctor_set(v___x_3162_, 1, v_msgData_3149_);
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___boxed(lean_object* v_msgData_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msgData_3164_, v___y_3165_, v___y_3166_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(lean_object* v_msg_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_ref_3173_; lean_object* v___x_3174_; lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3183_; 
v_ref_3173_ = lean_ctor_get(v___y_3170_, 2);
v___x_3174_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3169_, v___y_3170_, v___y_3171_);
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3177_ = v___x_3174_;
v_isShared_3178_ = v_isSharedCheck_3183_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3174_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3183_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
lean_inc(v_ref_3173_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v_ref_3173_);
lean_ctor_set(v___x_3179_, 1, v_a_3175_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set_tag(v___x_3177_, 1);
lean_ctor_set(v___x_3177_, 0, v___x_3179_);
v___x_3181_ = v___x_3177_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg___boxed(lean_object* v_msg_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
return v_res_3188_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3189_; double v___x_3190_; 
v___x_3189_ = lean_unsigned_to_nat(0u);
v___x_3190_ = lean_float_of_nat(v___x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object* v_cls_3194_, lean_object* v_msg_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_ref_3200_; lean_object* v___x_3201_; lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3248_; 
v_ref_3200_ = lean_ctor_get(v___y_3197_, 2);
v___x_3201_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3195_, v___y_3197_, v___y_3198_);
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3248_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3248_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v_traceState_3207_; lean_object* v_env_3208_; lean_object* v_nextMacroScope_3209_; lean_object* v_ngen_3210_; lean_object* v_auxDeclNGen_3211_; lean_object* v_cache_3212_; lean_object* v_recordedDeps_3213_; lean_object* v_messages_3214_; lean_object* v_infoState_3215_; lean_object* v_snapshotTasks_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3247_; 
v___x_3206_ = lean_st_ref_take(v___y_3198_);
v_traceState_3207_ = lean_ctor_get(v___x_3206_, 4);
v_env_3208_ = lean_ctor_get(v___x_3206_, 0);
v_nextMacroScope_3209_ = lean_ctor_get(v___x_3206_, 1);
v_ngen_3210_ = lean_ctor_get(v___x_3206_, 2);
v_auxDeclNGen_3211_ = lean_ctor_get(v___x_3206_, 3);
v_cache_3212_ = lean_ctor_get(v___x_3206_, 5);
v_recordedDeps_3213_ = lean_ctor_get(v___x_3206_, 6);
v_messages_3214_ = lean_ctor_get(v___x_3206_, 7);
v_infoState_3215_ = lean_ctor_get(v___x_3206_, 8);
v_snapshotTasks_3216_ = lean_ctor_get(v___x_3206_, 9);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3218_ = v___x_3206_;
v_isShared_3219_ = v_isSharedCheck_3247_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_snapshotTasks_3216_);
lean_inc(v_infoState_3215_);
lean_inc(v_messages_3214_);
lean_inc(v_recordedDeps_3213_);
lean_inc(v_cache_3212_);
lean_inc(v_traceState_3207_);
lean_inc(v_auxDeclNGen_3211_);
lean_inc(v_ngen_3210_);
lean_inc(v_nextMacroScope_3209_);
lean_inc(v_env_3208_);
lean_dec(v___x_3206_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3247_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
uint64_t v_tid_3220_; lean_object* v_traces_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3246_; 
v_tid_3220_ = lean_ctor_get_uint64(v_traceState_3207_, sizeof(void*)*1);
v_traces_3221_ = lean_ctor_get(v_traceState_3207_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v_traceState_3207_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3223_ = v_traceState_3207_;
v_isShared_3224_ = v_isSharedCheck_3246_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_traces_3221_);
lean_dec(v_traceState_3207_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3246_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; double v___x_3227_; uint8_t v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3225_ = lean_box(0);
v___x_3226_ = lean_box(0);
v___x_3227_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3228_ = 0;
v___x_3229_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3230_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3230_, 0, v_cls_3194_);
lean_ctor_set(v___x_3230_, 1, v___x_3226_);
lean_ctor_set(v___x_3230_, 2, v___x_3229_);
lean_ctor_set_float(v___x_3230_, sizeof(void*)*3, v___x_3227_);
lean_ctor_set_float(v___x_3230_, sizeof(void*)*3 + 8, v___x_3227_);
lean_ctor_set_uint8(v___x_3230_, sizeof(void*)*3 + 16, v___x_3228_);
v___x_3231_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3232_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3230_);
lean_ctor_set(v___x_3232_, 1, v_a_3202_);
lean_ctor_set(v___x_3232_, 2, v___x_3231_);
lean_inc(v_ref_3200_);
v___x_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3233_, 0, v_ref_3200_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = l_Lean_PersistentArray_push___redArg(v_traces_3221_, v___x_3233_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 0, v___x_3234_);
v___x_3236_ = v___x_3223_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3234_);
lean_ctor_set_uint64(v_reuseFailAlloc_3245_, sizeof(void*)*1, v_tid_3220_);
v___x_3236_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
lean_object* v___x_3238_; 
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 4, v___x_3236_);
v___x_3238_ = v___x_3218_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_env_3208_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_nextMacroScope_3209_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v_ngen_3210_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v_auxDeclNGen_3211_);
lean_ctor_set(v_reuseFailAlloc_3244_, 4, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3244_, 5, v_cache_3212_);
lean_ctor_set(v_reuseFailAlloc_3244_, 6, v_recordedDeps_3213_);
lean_ctor_set(v_reuseFailAlloc_3244_, 7, v_messages_3214_);
lean_ctor_set(v_reuseFailAlloc_3244_, 8, v_infoState_3215_);
lean_ctor_set(v_reuseFailAlloc_3244_, 9, v_snapshotTasks_3216_);
v___x_3238_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3239_ = lean_st_ref_put(v___y_3198_, v___x_3238_);
v___x_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3225_);
lean_ctor_set(v___x_3240_, 1, v___y_3196_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v___x_3240_);
v___x_3242_ = v___x_3204_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(lean_object* v_cls_3249_, lean_object* v_msg_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3249_, v_msg_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object* v_a_3256_, lean_object* v_x_3257_){
_start:
{
if (lean_obj_tag(v_x_3257_) == 0)
{
lean_object* v___x_3258_; 
v___x_3258_ = lean_box(0);
return v___x_3258_;
}
else
{
lean_object* v_key_3259_; lean_object* v_value_3260_; lean_object* v_tail_3261_; uint8_t v___x_3262_; 
v_key_3259_ = lean_ctor_get(v_x_3257_, 0);
v_value_3260_ = lean_ctor_get(v_x_3257_, 1);
v_tail_3261_ = lean_ctor_get(v_x_3257_, 2);
v___x_3262_ = l_Lean_instBEqFVarId_beq(v_key_3259_, v_a_3256_);
if (v___x_3262_ == 0)
{
v_x_3257_ = v_tail_3261_;
goto _start;
}
else
{
lean_object* v___x_3264_; 
lean_inc(v_value_3260_);
v___x_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3264_, 0, v_value_3260_);
return v___x_3264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_3265_, lean_object* v_x_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3265_, v_x_3266_);
lean_dec(v_x_3266_);
lean_dec(v_a_3265_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object* v_m_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v_buckets_3270_; lean_object* v___x_3271_; uint64_t v___x_3272_; uint64_t v___x_3273_; uint64_t v___x_3274_; uint64_t v_fold_3275_; uint64_t v___x_3276_; uint64_t v___x_3277_; uint64_t v___x_3278_; size_t v___x_3279_; size_t v___x_3280_; size_t v___x_3281_; size_t v___x_3282_; size_t v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_buckets_3270_ = lean_ctor_get(v_m_3268_, 1);
v___x_3271_ = lean_array_get_size(v_buckets_3270_);
v___x_3272_ = l_Lean_instHashableFVarId_hash(v_a_3269_);
v___x_3273_ = 32ULL;
v___x_3274_ = lean_uint64_shift_right(v___x_3272_, v___x_3273_);
v_fold_3275_ = lean_uint64_xor(v___x_3272_, v___x_3274_);
v___x_3276_ = 16ULL;
v___x_3277_ = lean_uint64_shift_right(v_fold_3275_, v___x_3276_);
v___x_3278_ = lean_uint64_xor(v_fold_3275_, v___x_3277_);
v___x_3279_ = lean_uint64_to_usize(v___x_3278_);
v___x_3280_ = lean_usize_of_nat(v___x_3271_);
v___x_3281_ = ((size_t)1ULL);
v___x_3282_ = lean_usize_sub(v___x_3280_, v___x_3281_);
v___x_3283_ = lean_usize_land(v___x_3279_, v___x_3282_);
v___x_3284_ = lean_array_uget_borrowed(v_buckets_3270_, v___x_3283_);
v___x_3285_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3269_, v___x_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object* v_m_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3286_, v_a_3287_);
lean_dec(v_a_3287_);
lean_dec_ref(v_m_3286_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object* v___x_3289_, lean_object* v_m_3290_, lean_object* v_e_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
uint8_t v___x_17738__boxed_3296_; lean_object* v_res_3297_; 
v___x_17738__boxed_3296_ = lean_unbox(v___x_3289_);
v_res_3297_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(v___x_17738__boxed_3296_, v_m_3290_, v_e_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec_ref(v_e_3291_);
return v_res_3297_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_unsigned_to_nat(16u);
v___x_3300_ = lean_mk_array(v___x_3299_, v___x_3298_);
return v___x_3300_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3301_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0);
v___x_3302_ = lean_unsigned_to_nat(0u);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v___x_3301_);
return v___x_3303_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3307_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4));
v___x_3308_ = lean_unsigned_to_nat(4u);
v___x_3309_ = lean_unsigned_to_nat(390u);
v___x_3310_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3));
v___x_3311_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3312_ = l_mkPanicMessageWithDecl(v___x_3311_, v___x_3310_, v___x_3309_, v___x_3308_, v___x_3307_);
return v___x_3312_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6));
v___x_3315_ = l_Lean_stringToMessageData(v___x_3314_);
return v___x_3315_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12));
v___x_3326_ = l_Lean_Name_append(v___x_3325_, v___x_3324_);
return v___x_3326_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14));
v___x_3329_ = l_Lean_stringToMessageData(v___x_3328_);
return v___x_3329_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16));
v___x_3332_ = l_Lean_stringToMessageData(v___x_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(lean_object* v_m_3333_, lean_object* v_fvarId_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3333_, v_fvarId_3334_);
if (lean_obj_tag(v___x_3339_) == 1)
{
lean_object* v_val_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3450_; 
v_val_3340_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3342_ = v___x_3339_;
v_isShared_3343_ = v_isSharedCheck_3450_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_val_3340_);
lean_dec(v___x_3339_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3450_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v_fst_3344_; lean_object* v_snd_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3449_; 
v_fst_3344_ = lean_ctor_get(v_val_3340_, 0);
v_snd_3345_ = lean_ctor_get(v_val_3340_, 1);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_val_3340_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3347_ = v_val_3340_;
v_isShared_3348_ = v_isSharedCheck_3449_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_snd_3345_);
lean_inc(v_fst_3344_);
lean_dec(v_val_3340_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3449_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v_tempMark_3349_; lean_object* v_doneMark_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; 
v_tempMark_3349_ = lean_ctor_get(v_a_3335_, 0);
v_doneMark_3350_ = lean_ctor_get(v_a_3335_, 1);
v___x_3351_ = l_Lean_LocalDecl_fvarId(v_fst_3344_);
v___x_3352_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_doneMark_3350_, v___x_3351_);
if (v___x_3352_ == 0)
{
lean_object* v_toCold_3353_; lean_object* v_options_3354_; lean_object* v_inheritedTraceOptions_3355_; uint8_t v_hasTrace_3356_; uint8_t v___x_3357_; lean_object* v___x_3358_; lean_object* v___f_3359_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3417_; lean_object* v_tempMark_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; 
lean_del_object(v___x_3347_);
lean_del_object(v___x_3342_);
v_toCold_3353_ = lean_ctor_get(v_a_3336_, 0);
v_options_3354_ = lean_ctor_get(v_toCold_3353_, 2);
v_inheritedTraceOptions_3355_ = lean_ctor_get(v_toCold_3353_, 11);
v_hasTrace_3356_ = lean_ctor_get_uint8(v_options_3354_, sizeof(void*)*1);
v___x_3357_ = 1;
v___x_3358_ = lean_box(v___x_3357_);
v___f_3359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3359_, 0, v___x_3358_);
lean_closure_set(v___f_3359_, 1, v_m_3333_);
if (v_hasTrace_3356_ == 0)
{
lean_inc_ref(v_tempMark_3349_);
v___y_3417_ = v_a_3335_;
v_tempMark_3418_ = v_tempMark_3349_;
v___y_3419_ = v_a_3336_;
v___y_3420_ = v_a_3337_;
goto v___jp_3416_;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3426_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3427_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_3428_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3355_, v_options_3354_, v___x_3427_);
if (v___x_3428_ == 0)
{
lean_inc_ref(v_tempMark_3349_);
v___y_3417_ = v_a_3335_;
v_tempMark_3418_ = v_tempMark_3349_;
v___y_3419_ = v_a_3336_;
v___y_3420_ = v_a_3337_;
goto v___jp_3416_;
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3429_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15);
lean_inc(v___x_3351_);
v___x_3430_ = l_Lean_mkFVar(v___x_3351_);
v___x_3431_ = l_Lean_MessageData_ofExpr(v___x_3430_);
v___x_3432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3429_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3432_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = l_Lean_LocalDecl_type(v_fst_3344_);
v___x_3436_ = l_Lean_MessageData_ofExpr(v___x_3435_);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3434_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v___x_3426_, v___x_3437_, v_a_3335_, v_a_3336_, v_a_3337_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v_snd_3440_; lean_object* v_tempMark_3441_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
v_snd_3440_ = lean_ctor_get(v_a_3439_, 1);
lean_inc(v_snd_3440_);
lean_dec(v_a_3439_);
v_tempMark_3441_ = lean_ctor_get(v_snd_3440_, 0);
lean_inc_ref(v_tempMark_3441_);
v___y_3417_ = v_snd_3440_;
v_tempMark_3418_ = v_tempMark_3441_;
v___y_3419_ = v_a_3336_;
v___y_3420_ = v_a_3337_;
goto v___jp_3416_;
}
else
{
lean_dec_ref(v___f_3359_);
lean_dec(v___x_3351_);
lean_dec(v_snd_3345_);
lean_dec(v_fst_3344_);
return v___x_3438_;
}
}
}
v___jp_3360_:
{
uint8_t v___x_3364_; 
v___x_3364_ = l_Lean_LocalDecl_isLet(v_fst_3344_, v___x_3357_);
if (v___x_3364_ == 0)
{
lean_object* v_tempMark_3365_; lean_object* v_doneMark_3366_; lean_object* v_newDecls_3367_; lean_object* v_newArgs_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3413_; 
v_tempMark_3365_ = lean_ctor_get(v___y_3361_, 0);
v_doneMark_3366_ = lean_ctor_get(v___y_3361_, 1);
v_newDecls_3367_ = lean_ctor_get(v___y_3361_, 2);
v_newArgs_3368_ = lean_ctor_get(v___y_3361_, 3);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___y_3361_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3370_ = v___y_3361_;
v_isShared_3371_ = v_isSharedCheck_3413_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_newArgs_3368_);
lean_inc(v_newDecls_3367_);
lean_inc(v_doneMark_3366_);
lean_inc(v_tempMark_3365_);
lean_dec(v___y_3361_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3413_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3372_ = lean_box(0);
lean_inc(v___x_3351_);
v___x_3373_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_tempMark_3365_, v___x_3351_, v___x_3372_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3373_);
v___x_3375_ = v___x_3370_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_doneMark_3366_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_newDecls_3367_);
lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_newArgs_3368_);
v___x_3375_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3376_ = l_Lean_LocalDecl_type(v_fst_3344_);
v___x_3377_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1);
v___x_3378_ = lean_st_mk_ref(v___x_3377_);
v___x_3379_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v___f_3359_, v___x_3376_, v___x_3378_, v___x_3375_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3411_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3382_ = v___x_3379_;
v_isShared_3383_ = v_isSharedCheck_3411_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3411_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v_snd_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3409_; 
v_snd_3384_ = lean_ctor_get(v_a_3380_, 1);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_a_3380_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; 
v_unused_3410_ = lean_ctor_get(v_a_3380_, 0);
lean_dec(v_unused_3410_);
v___x_3386_ = v_a_3380_;
v_isShared_3387_ = v_isSharedCheck_3409_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_snd_3384_);
lean_dec(v_a_3380_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3409_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3388_; lean_object* v_tempMark_3389_; lean_object* v_doneMark_3390_; lean_object* v_newDecls_3391_; lean_object* v_newArgs_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3408_; 
v___x_3388_ = lean_st_ref_get(v___x_3378_);
lean_dec(v___x_3378_);
lean_dec(v___x_3388_);
v_tempMark_3389_ = lean_ctor_get(v_snd_3384_, 0);
v_doneMark_3390_ = lean_ctor_get(v_snd_3384_, 1);
v_newDecls_3391_ = lean_ctor_get(v_snd_3384_, 2);
v_newArgs_3392_ = lean_ctor_get(v_snd_3384_, 3);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_snd_3384_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3394_ = v_snd_3384_;
v_isShared_3395_ = v_isSharedCheck_3408_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_newArgs_3392_);
lean_inc(v_newDecls_3391_);
lean_inc(v_doneMark_3390_);
lean_inc(v_tempMark_3389_);
lean_dec(v_snd_3384_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3408_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3400_; 
v___x_3396_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_doneMark_3390_, v___x_3351_, v___x_3372_);
v___x_3397_ = lean_array_push(v_newDecls_3391_, v_fst_3344_);
v___x_3398_ = lean_array_push(v_newArgs_3392_, v_snd_3345_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 3, v___x_3398_);
lean_ctor_set(v___x_3394_, 2, v___x_3397_);
lean_ctor_set(v___x_3394_, 1, v___x_3396_);
v___x_3400_ = v___x_3394_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_tempMark_3389_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v___x_3396_);
lean_ctor_set(v_reuseFailAlloc_3407_, 2, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3407_, 3, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3402_; 
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 1, v___x_3400_);
lean_ctor_set(v___x_3386_, 0, v___x_3372_);
v___x_3402_ = v___x_3386_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3404_; 
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3402_);
v___x_3404_ = v___x_3382_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3378_);
lean_dec(v___x_3351_);
lean_dec(v_snd_3345_);
lean_dec(v_fst_3344_);
return v___x_3379_;
}
}
}
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec_ref(v___f_3359_);
lean_dec(v___x_3351_);
lean_dec(v_snd_3345_);
lean_dec(v_fst_3344_);
v___x_3414_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5);
v___x_3415_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v___x_3414_, v___y_3361_, v___y_3362_, v___y_3363_);
return v___x_3415_;
}
}
v___jp_3416_:
{
uint8_t v___x_3421_; 
v___x_3421_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_tempMark_3418_, v___x_3351_);
lean_dec_ref(v_tempMark_3418_);
if (v___x_3421_ == 0)
{
v___y_3361_ = v___y_3417_;
v___y_3362_ = v___y_3419_;
v___y_3363_ = v___y_3420_;
goto v___jp_3360_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec_ref(v___y_3417_);
v___x_3422_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7);
v___x_3423_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v___x_3422_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v_snd_3425_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
v_snd_3425_ = lean_ctor_get(v_a_3424_, 1);
lean_inc(v_snd_3425_);
lean_dec(v_a_3424_);
v___y_3361_ = v_snd_3425_;
v___y_3362_ = v___y_3419_;
v___y_3363_ = v___y_3420_;
goto v___jp_3360_;
}
else
{
lean_dec_ref(v___f_3359_);
lean_dec(v___x_3351_);
lean_dec(v_snd_3345_);
lean_dec(v_fst_3344_);
return v___x_3423_;
}
}
}
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
lean_dec(v___x_3351_);
lean_dec(v_snd_3345_);
lean_dec(v_fst_3344_);
lean_dec_ref(v_m_3333_);
v___x_3442_ = lean_box(0);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 1, v_a_3335_);
lean_ctor_set(v___x_3347_, 0, v___x_3442_);
v___x_3444_ = v___x_3347_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_a_3335_);
v___x_3444_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set_tag(v___x_3342_, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3444_);
v___x_3446_ = v___x_3342_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec(v___x_3339_);
lean_dec_ref(v_m_3333_);
v___x_3451_ = lean_box(0);
v___x_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
lean_ctor_set(v___x_3452_, 1, v_a_3335_);
v___x_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t v___x_3454_, lean_object* v_m_3455_, lean_object* v_e_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v___y_3462_; uint8_t v___x_3466_; 
v___x_3466_ = l_Lean_Expr_hasFVar(v_e_3456_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
lean_dec_ref(v_m_3455_);
v___x_3467_ = lean_box(v___x_3466_);
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
lean_ctor_set(v___x_3468_, 1, v___y_3457_);
v___x_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
return v___x_3469_;
}
else
{
uint8_t v___x_3470_; 
v___x_3470_ = l_Lean_Expr_isFVar(v_e_3456_);
if (v___x_3470_ == 0)
{
lean_dec_ref(v_m_3455_);
v___y_3462_ = v___y_3457_;
goto v___jp_3461_;
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = l_Lean_Expr_fvarId_x21(v_e_3456_);
v___x_3472_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3455_, v___x_3471_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___x_3471_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v_snd_3474_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3473_);
lean_dec_ref_known(v___x_3472_, 1);
v_snd_3474_ = lean_ctor_get(v_a_3473_, 1);
lean_inc(v_snd_3474_);
lean_dec(v_a_3473_);
v___y_3462_ = v_snd_3474_;
goto v___jp_3461_;
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
v_a_3475_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3472_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3472_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
}
v___jp_3461_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3463_ = lean_box(v___x_3454_);
v___x_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v___y_3462_);
v___x_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
return v___x_3465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object* v_m_3483_, lean_object* v_fvarId_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3483_, v_fvarId_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
lean_dec(v_fvarId_3484_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object* v_00_u03b2_3490_, lean_object* v_m_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3491_, v_a_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object* v_00_u03b2_3494_, lean_object* v_m_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(v_00_u03b2_3494_, v_m_3495_, v_a_3496_);
lean_dec(v_a_3496_);
lean_dec_ref(v_m_3495_);
return v_res_3497_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object* v_00_u03b2_3498_, lean_object* v_m_3499_, lean_object* v_a_3500_){
_start:
{
uint8_t v___x_3501_; 
v___x_3501_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_3499_, v_a_3500_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object* v_00_u03b2_3502_, lean_object* v_m_3503_, lean_object* v_a_3504_){
_start:
{
uint8_t v_res_3505_; lean_object* v_r_3506_; 
v_res_3505_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(v_00_u03b2_3502_, v_m_3503_, v_a_3504_);
lean_dec(v_a_3504_);
lean_dec_ref(v_m_3503_);
v_r_3506_ = lean_box(v_res_3505_);
return v_r_3506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object* v_00_u03b2_3507_, lean_object* v_m_3508_, lean_object* v_a_3509_, lean_object* v_b_3510_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_m_3508_, v_a_3509_, v_b_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object* v_00_u03b1_3512_, lean_object* v_msg_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3513_, v___y_3515_, v___y_3516_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object* v_00_u03b1_3519_, lean_object* v_msg_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v_00_u03b1_3519_, v_msg_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec_ref(v___y_3521_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object* v_00_u03b2_3526_, lean_object* v_a_3527_, lean_object* v_x_3528_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3527_, v_x_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3530_, lean_object* v_a_3531_, lean_object* v_x_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(v_00_u03b2_3530_, v_a_3531_, v_x_3532_);
lean_dec(v_x_3532_);
lean_dec(v_a_3531_);
return v_res_3533_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_object* v_00_u03b2_3534_, lean_object* v_a_3535_, lean_object* v_x_3536_){
_start:
{
uint8_t v___x_3537_; 
v___x_3537_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3535_, v_x_3536_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3538_, lean_object* v_a_3539_, lean_object* v_x_3540_){
_start:
{
uint8_t v_res_3541_; lean_object* v_r_3542_; 
v_res_3541_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(v_00_u03b2_3538_, v_a_3539_, v_x_3540_);
lean_dec(v_x_3540_);
lean_dec(v_a_3539_);
v_r_3542_ = lean_box(v_res_3541_);
return v_r_3542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(lean_object* v_00_u03b2_3543_, lean_object* v_data_3544_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_data_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(lean_object* v_00_u03b2_3546_, lean_object* v_m_3547_, lean_object* v_a_3548_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_3547_, v_a_3548_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3550_, lean_object* v_m_3551_, lean_object* v_a_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(v_00_u03b2_3550_, v_m_3551_, v_a_3552_);
lean_dec_ref(v_a_3552_);
lean_dec_ref(v_m_3551_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(lean_object* v_00_u03b2_3554_, lean_object* v_m_3555_, lean_object* v_a_3556_, lean_object* v_b_3557_){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_3555_, v_a_3556_, v_b_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_3559_, lean_object* v_i_3560_, lean_object* v_source_3561_, lean_object* v_target_3562_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v_i_3560_, v_source_3561_, v_target_3562_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_3564_, lean_object* v_a_3565_, lean_object* v_x_3566_){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_3565_, v_x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3568_, lean_object* v_a_3569_, lean_object* v_x_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(v_00_u03b2_3568_, v_a_3569_, v_x_3570_);
lean_dec(v_x_3570_);
lean_dec_ref(v_a_3569_);
return v_res_3571_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3572_, lean_object* v_a_3573_, lean_object* v_x_3574_){
_start:
{
uint8_t v___x_3575_; 
v___x_3575_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3573_, v_x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3576_, lean_object* v_a_3577_, lean_object* v_x_3578_){
_start:
{
uint8_t v_res_3579_; lean_object* v_r_3580_; 
v_res_3579_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(v_00_u03b2_3576_, v_a_3577_, v_x_3578_);
lean_dec(v_x_3578_);
lean_dec_ref(v_a_3577_);
v_r_3580_ = lean_box(v_res_3579_);
return v_r_3580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b2_3581_, lean_object* v_data_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_data_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13(lean_object* v_00_u03b2_3584_, lean_object* v_a_3585_, lean_object* v_b_3586_, lean_object* v_x_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3585_, v_b_3586_, v_x_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_3589_, lean_object* v_x_3590_, lean_object* v_x_3591_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_x_3590_, v_x_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17(lean_object* v_00_u03b2_3593_, lean_object* v_i_3594_, lean_object* v_source_3595_, lean_object* v_target_3596_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v_i_3594_, v_source_3595_, v_target_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18(lean_object* v_00_u03b2_3598_, lean_object* v_x_3599_, lean_object* v_x_3600_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_x_3599_, v_x_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object* v_msg_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v___f_3607_; lean_object* v___x_7408__overap_3608_; lean_object* v___x_3609_; 
v___f_3607_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___closed__0));
v___x_7408__overap_3608_ = lean_panic_fn_borrowed(v___f_3607_, v_msg_3603_);
lean_inc(v___y_3605_);
lean_inc_ref(v___y_3604_);
v___x_3609_ = lean_apply_3(v___x_7408__overap_3608_, v___y_3604_, v___y_3605_, lean_box(0));
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___boxed(lean_object* v_msg_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v_msg_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object* v_newDecls_3615_, lean_object* v_newArgs_3616_, lean_object* v_____r_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3622_, 0, v_newDecls_3615_);
lean_ctor_set(v___x_3622_, 1, v_newArgs_3616_);
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
lean_ctor_set(v___x_3623_, 1, v___y_3618_);
v___x_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object* v_newDecls_3625_, lean_object* v_newArgs_3626_, lean_object* v_____r_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3625_, v_newArgs_3626_, v_____r_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(lean_object* v_cls_3633_, lean_object* v_msg_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v_ref_3638_; lean_object* v___x_3639_; lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3685_; 
v_ref_3638_ = lean_ctor_get(v___y_3635_, 2);
v___x_3639_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3634_, v___y_3635_, v___y_3636_);
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3642_ = v___x_3639_;
v_isShared_3643_ = v_isSharedCheck_3685_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3639_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3685_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v_traceState_3645_; lean_object* v_env_3646_; lean_object* v_nextMacroScope_3647_; lean_object* v_ngen_3648_; lean_object* v_auxDeclNGen_3649_; lean_object* v_cache_3650_; lean_object* v_recordedDeps_3651_; lean_object* v_messages_3652_; lean_object* v_infoState_3653_; lean_object* v_snapshotTasks_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3684_; 
v___x_3644_ = lean_st_ref_take(v___y_3636_);
v_traceState_3645_ = lean_ctor_get(v___x_3644_, 4);
v_env_3646_ = lean_ctor_get(v___x_3644_, 0);
v_nextMacroScope_3647_ = lean_ctor_get(v___x_3644_, 1);
v_ngen_3648_ = lean_ctor_get(v___x_3644_, 2);
v_auxDeclNGen_3649_ = lean_ctor_get(v___x_3644_, 3);
v_cache_3650_ = lean_ctor_get(v___x_3644_, 5);
v_recordedDeps_3651_ = lean_ctor_get(v___x_3644_, 6);
v_messages_3652_ = lean_ctor_get(v___x_3644_, 7);
v_infoState_3653_ = lean_ctor_get(v___x_3644_, 8);
v_snapshotTasks_3654_ = lean_ctor_get(v___x_3644_, 9);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3656_ = v___x_3644_;
v_isShared_3657_ = v_isSharedCheck_3684_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_snapshotTasks_3654_);
lean_inc(v_infoState_3653_);
lean_inc(v_messages_3652_);
lean_inc(v_recordedDeps_3651_);
lean_inc(v_cache_3650_);
lean_inc(v_traceState_3645_);
lean_inc(v_auxDeclNGen_3649_);
lean_inc(v_ngen_3648_);
lean_inc(v_nextMacroScope_3647_);
lean_inc(v_env_3646_);
lean_dec(v___x_3644_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3684_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
uint64_t v_tid_3658_; lean_object* v_traces_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3683_; 
v_tid_3658_ = lean_ctor_get_uint64(v_traceState_3645_, sizeof(void*)*1);
v_traces_3659_ = lean_ctor_get(v_traceState_3645_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_traceState_3645_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3661_ = v_traceState_3645_;
v_isShared_3662_ = v_isSharedCheck_3683_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_traces_3659_);
lean_dec(v_traceState_3645_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3683_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; double v___x_3665_; uint8_t v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3674_; 
v___x_3663_ = lean_box(0);
v___x_3664_ = lean_box(0);
v___x_3665_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3666_ = 0;
v___x_3667_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3668_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3668_, 0, v_cls_3633_);
lean_ctor_set(v___x_3668_, 1, v___x_3664_);
lean_ctor_set(v___x_3668_, 2, v___x_3667_);
lean_ctor_set_float(v___x_3668_, sizeof(void*)*3, v___x_3665_);
lean_ctor_set_float(v___x_3668_, sizeof(void*)*3 + 8, v___x_3665_);
lean_ctor_set_uint8(v___x_3668_, sizeof(void*)*3 + 16, v___x_3666_);
v___x_3669_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3670_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3668_);
lean_ctor_set(v___x_3670_, 1, v_a_3640_);
lean_ctor_set(v___x_3670_, 2, v___x_3669_);
lean_inc(v_ref_3638_);
v___x_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3671_, 0, v_ref_3638_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
v___x_3672_ = l_Lean_PersistentArray_push___redArg(v_traces_3659_, v___x_3671_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 0, v___x_3672_);
v___x_3674_ = v___x_3661_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3672_);
lean_ctor_set_uint64(v_reuseFailAlloc_3682_, sizeof(void*)*1, v_tid_3658_);
v___x_3674_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3676_; 
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 4, v___x_3674_);
v___x_3676_ = v___x_3656_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_env_3646_);
lean_ctor_set(v_reuseFailAlloc_3681_, 1, v_nextMacroScope_3647_);
lean_ctor_set(v_reuseFailAlloc_3681_, 2, v_ngen_3648_);
lean_ctor_set(v_reuseFailAlloc_3681_, 3, v_auxDeclNGen_3649_);
lean_ctor_set(v_reuseFailAlloc_3681_, 4, v___x_3674_);
lean_ctor_set(v_reuseFailAlloc_3681_, 5, v_cache_3650_);
lean_ctor_set(v_reuseFailAlloc_3681_, 6, v_recordedDeps_3651_);
lean_ctor_set(v_reuseFailAlloc_3681_, 7, v_messages_3652_);
lean_ctor_set(v_reuseFailAlloc_3681_, 8, v_infoState_3653_);
lean_ctor_set(v_reuseFailAlloc_3681_, 9, v_snapshotTasks_3654_);
v___x_3676_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; lean_object* v___x_3679_; 
v___x_3677_ = lean_st_ref_put(v___y_3636_, v___x_3676_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3663_);
v___x_3679_ = v___x_3642_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3663_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(lean_object* v_cls_3686_, lean_object* v_msg_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3686_, v_msg_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(size_t v_sz_3692_, size_t v_i_3693_, lean_object* v_bs_3694_){
_start:
{
uint8_t v___x_3695_; 
v___x_3695_ = lean_usize_dec_lt(v_i_3693_, v_sz_3692_);
if (v___x_3695_ == 0)
{
return v_bs_3694_;
}
else
{
lean_object* v_v_3696_; lean_object* v___x_3697_; lean_object* v_bs_x27_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; size_t v___x_3701_; size_t v___x_3702_; lean_object* v___x_3703_; 
v_v_3696_ = lean_array_uget(v_bs_3694_, v_i_3693_);
v___x_3697_ = lean_unsigned_to_nat(0u);
v_bs_x27_3698_ = lean_array_uset(v_bs_3694_, v_i_3693_, v___x_3697_);
v___x_3699_ = l_Lean_LocalDecl_fvarId(v_v_3696_);
lean_dec(v_v_3696_);
v___x_3700_ = l_Lean_mkFVar(v___x_3699_);
v___x_3701_ = ((size_t)1ULL);
v___x_3702_ = lean_usize_add(v_i_3693_, v___x_3701_);
v___x_3703_ = lean_array_uset(v_bs_x27_3698_, v_i_3693_, v___x_3700_);
v_i_3693_ = v___x_3702_;
v_bs_3694_ = v___x_3703_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(lean_object* v_sz_3705_, lean_object* v_i_3706_, lean_object* v_bs_3707_){
_start:
{
size_t v_sz_boxed_3708_; size_t v_i_boxed_3709_; lean_object* v_res_3710_; 
v_sz_boxed_3708_ = lean_unbox_usize(v_sz_3705_);
lean_dec(v_sz_3705_);
v_i_boxed_3709_ = lean_unbox_usize(v_i_3706_);
lean_dec(v_i_3706_);
v_res_3710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_boxed_3708_, v_i_boxed_3709_, v_bs_3707_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(lean_object* v___x_3711_, lean_object* v_as_3712_, size_t v_sz_3713_, size_t v_i_3714_, lean_object* v_b_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
uint8_t v___x_3720_; 
v___x_3720_ = lean_usize_dec_lt(v_i_3714_, v_sz_3713_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
lean_dec_ref(v___x_3711_);
v___x_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3721_, 0, v_b_3715_);
lean_ctor_set(v___x_3721_, 1, v___y_3716_);
v___x_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
return v___x_3722_;
}
else
{
lean_object* v___x_3723_; lean_object* v_a_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3723_ = lean_box(0);
v_a_3724_ = lean_array_uget_borrowed(v_as_3712_, v_i_3714_);
v___x_3725_ = l_Lean_LocalDecl_fvarId(v_a_3724_);
lean_inc_ref(v___x_3711_);
v___x_3726_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v___x_3711_, v___x_3725_, v___y_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___x_3725_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v_snd_3728_; size_t v___x_3729_; size_t v___x_3730_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
v_snd_3728_ = lean_ctor_get(v_a_3727_, 1);
lean_inc(v_snd_3728_);
lean_dec(v_a_3727_);
v___x_3729_ = ((size_t)1ULL);
v___x_3730_ = lean_usize_add(v_i_3714_, v___x_3729_);
v_i_3714_ = v___x_3730_;
v_b_3715_ = v___x_3723_;
v___y_3716_ = v_snd_3728_;
goto _start;
}
else
{
lean_dec_ref(v___x_3711_);
return v___x_3726_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object* v___x_3732_, lean_object* v_as_3733_, lean_object* v_sz_3734_, lean_object* v_i_3735_, lean_object* v_b_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
size_t v_sz_boxed_3741_; size_t v_i_boxed_3742_; lean_object* v_res_3743_; 
v_sz_boxed_3741_ = lean_unbox_usize(v_sz_3734_);
lean_dec(v_sz_3734_);
v_i_boxed_3742_ = lean_unbox_usize(v_i_3735_);
lean_dec(v_i_3735_);
v_res_3743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v___x_3732_, v_as_3733_, v_sz_boxed_3741_, v_i_boxed_3742_, v_b_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec_ref(v_as_3733_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object* v_a_3744_, lean_object* v_a_3745_){
_start:
{
if (lean_obj_tag(v_a_3744_) == 0)
{
lean_object* v___x_3746_; 
v___x_3746_ = l_List_reverse___redArg(v_a_3745_);
return v___x_3746_;
}
else
{
lean_object* v_head_3747_; lean_object* v_tail_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3757_; 
v_head_3747_ = lean_ctor_get(v_a_3744_, 0);
v_tail_3748_ = lean_ctor_get(v_a_3744_, 1);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_a_3744_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3750_ = v_a_3744_;
v_isShared_3751_ = v_isSharedCheck_3757_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_tail_3748_);
lean_inc(v_head_3747_);
lean_dec(v_a_3744_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3757_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3752_; lean_object* v___x_3754_; 
v___x_3752_ = l_Lean_MessageData_ofExpr(v_head_3747_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v_a_3745_);
lean_ctor_set(v___x_3750_, 0, v___x_3752_);
v___x_3754_ = v___x_3750_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3752_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_a_3745_);
v___x_3754_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
v_a_3744_ = v_tail_3748_;
v_a_3745_ = v___x_3754_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(lean_object* v_a_3758_, lean_object* v_b_3759_, lean_object* v_x_3760_){
_start:
{
if (lean_obj_tag(v_x_3760_) == 0)
{
lean_dec(v_b_3759_);
lean_dec(v_a_3758_);
return v_x_3760_;
}
else
{
lean_object* v_key_3761_; lean_object* v_value_3762_; lean_object* v_tail_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3775_; 
v_key_3761_ = lean_ctor_get(v_x_3760_, 0);
v_value_3762_ = lean_ctor_get(v_x_3760_, 1);
v_tail_3763_ = lean_ctor_get(v_x_3760_, 2);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_x_3760_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3765_ = v_x_3760_;
v_isShared_3766_ = v_isSharedCheck_3775_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_tail_3763_);
lean_inc(v_value_3762_);
lean_inc(v_key_3761_);
lean_dec(v_x_3760_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3775_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
uint8_t v___x_3767_; 
v___x_3767_ = l_Lean_instBEqFVarId_beq(v_key_3761_, v_a_3758_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; lean_object* v___x_3770_; 
v___x_3768_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_3758_, v_b_3759_, v_tail_3763_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 2, v___x_3768_);
v___x_3770_ = v___x_3765_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_key_3761_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v_value_3762_);
lean_ctor_set(v_reuseFailAlloc_3771_, 2, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
else
{
lean_object* v___x_3773_; 
lean_dec(v_value_3762_);
lean_dec(v_key_3761_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 1, v_b_3759_);
lean_ctor_set(v___x_3765_, 0, v_a_3758_);
v___x_3773_ = v___x_3765_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3758_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_b_3759_);
lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_tail_3763_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(lean_object* v_m_3776_, lean_object* v_a_3777_, lean_object* v_b_3778_){
_start:
{
lean_object* v_size_3779_; lean_object* v_buckets_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3823_; 
v_size_3779_ = lean_ctor_get(v_m_3776_, 0);
v_buckets_3780_ = lean_ctor_get(v_m_3776_, 1);
v_isSharedCheck_3823_ = !lean_is_exclusive(v_m_3776_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3782_ = v_m_3776_;
v_isShared_3783_ = v_isSharedCheck_3823_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_buckets_3780_);
lean_inc(v_size_3779_);
lean_dec(v_m_3776_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3823_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3784_; uint64_t v___x_3785_; uint64_t v___x_3786_; uint64_t v___x_3787_; uint64_t v_fold_3788_; uint64_t v___x_3789_; uint64_t v___x_3790_; uint64_t v___x_3791_; size_t v___x_3792_; size_t v___x_3793_; size_t v___x_3794_; size_t v___x_3795_; size_t v___x_3796_; lean_object* v_bkt_3797_; uint8_t v___x_3798_; 
v___x_3784_ = lean_array_get_size(v_buckets_3780_);
v___x_3785_ = l_Lean_instHashableFVarId_hash(v_a_3777_);
v___x_3786_ = 32ULL;
v___x_3787_ = lean_uint64_shift_right(v___x_3785_, v___x_3786_);
v_fold_3788_ = lean_uint64_xor(v___x_3785_, v___x_3787_);
v___x_3789_ = 16ULL;
v___x_3790_ = lean_uint64_shift_right(v_fold_3788_, v___x_3789_);
v___x_3791_ = lean_uint64_xor(v_fold_3788_, v___x_3790_);
v___x_3792_ = lean_uint64_to_usize(v___x_3791_);
v___x_3793_ = lean_usize_of_nat(v___x_3784_);
v___x_3794_ = ((size_t)1ULL);
v___x_3795_ = lean_usize_sub(v___x_3793_, v___x_3794_);
v___x_3796_ = lean_usize_land(v___x_3792_, v___x_3795_);
v_bkt_3797_ = lean_array_uget_borrowed(v_buckets_3780_, v___x_3796_);
v___x_3798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3777_, v_bkt_3797_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3799_; lean_object* v_size_x27_3800_; lean_object* v___x_3801_; lean_object* v_buckets_x27_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
v___x_3799_ = lean_unsigned_to_nat(1u);
v_size_x27_3800_ = lean_nat_add(v_size_3779_, v___x_3799_);
lean_dec(v_size_3779_);
lean_inc(v_bkt_3797_);
v___x_3801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3801_, 0, v_a_3777_);
lean_ctor_set(v___x_3801_, 1, v_b_3778_);
lean_ctor_set(v___x_3801_, 2, v_bkt_3797_);
v_buckets_x27_3802_ = lean_array_uset(v_buckets_3780_, v___x_3796_, v___x_3801_);
v___x_3803_ = lean_unsigned_to_nat(4u);
v___x_3804_ = lean_nat_mul(v_size_x27_3800_, v___x_3803_);
v___x_3805_ = lean_unsigned_to_nat(3u);
v___x_3806_ = lean_nat_div(v___x_3804_, v___x_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_array_get_size(v_buckets_x27_3802_);
v___x_3808_ = lean_nat_dec_le(v___x_3806_, v___x_3807_);
lean_dec(v___x_3806_);
if (v___x_3808_ == 0)
{
lean_object* v_val_3809_; lean_object* v___x_3811_; 
v_val_3809_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_3802_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 1, v_val_3809_);
lean_ctor_set(v___x_3782_, 0, v_size_x27_3800_);
v___x_3811_ = v___x_3782_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_size_x27_3800_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_val_3809_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
else
{
lean_object* v___x_3814_; 
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 1, v_buckets_x27_3802_);
lean_ctor_set(v___x_3782_, 0, v_size_x27_3800_);
v___x_3814_ = v___x_3782_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_size_x27_3800_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_buckets_x27_3802_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
else
{
lean_object* v___x_3816_; lean_object* v_buckets_x27_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3821_; 
lean_inc(v_bkt_3797_);
v___x_3816_ = lean_box(0);
v_buckets_x27_3817_ = lean_array_uset(v_buckets_3780_, v___x_3796_, v___x_3816_);
v___x_3818_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_3777_, v_b_3778_, v_bkt_3797_);
v___x_3819_ = lean_array_uset(v_buckets_x27_3817_, v___x_3796_, v___x_3818_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 1, v___x_3819_);
v___x_3821_ = v___x_3782_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_size_3779_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v___x_3819_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(lean_object* v_as_3824_, size_t v_sz_3825_, size_t v_i_3826_, lean_object* v_b_3827_){
_start:
{
uint8_t v___x_3829_; 
v___x_3829_ = lean_usize_dec_lt(v_i_3826_, v_sz_3825_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; 
v___x_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3830_, 0, v_b_3827_);
return v___x_3830_;
}
else
{
lean_object* v_snd_3831_; lean_object* v_fst_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3867_; 
v_snd_3831_ = lean_ctor_get(v_b_3827_, 1);
v_fst_3832_ = lean_ctor_get(v_b_3827_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_b_3827_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3834_ = v_b_3827_;
v_isShared_3835_ = v_isSharedCheck_3867_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_snd_3831_);
lean_inc(v_fst_3832_);
lean_dec(v_b_3827_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3867_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v_array_3836_; lean_object* v_start_3837_; lean_object* v_stop_3838_; uint8_t v___x_3839_; 
v_array_3836_ = lean_ctor_get(v_snd_3831_, 0);
v_start_3837_ = lean_ctor_get(v_snd_3831_, 1);
v_stop_3838_ = lean_ctor_get(v_snd_3831_, 2);
v___x_3839_ = lean_nat_dec_lt(v_start_3837_, v_stop_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3841_; 
if (v_isShared_3835_ == 0)
{
v___x_3841_ = v___x_3834_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_fst_3832_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_snd_3831_);
v___x_3841_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3842_; 
v___x_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3841_);
return v___x_3842_;
}
}
else
{
lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3863_; 
lean_inc(v_stop_3838_);
lean_inc(v_start_3837_);
lean_inc_ref(v_array_3836_);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_snd_3831_);
if (v_isSharedCheck_3863_ == 0)
{
lean_object* v_unused_3864_; lean_object* v_unused_3865_; lean_object* v_unused_3866_; 
v_unused_3864_ = lean_ctor_get(v_snd_3831_, 2);
lean_dec(v_unused_3864_);
v_unused_3865_ = lean_ctor_get(v_snd_3831_, 1);
lean_dec(v_unused_3865_);
v_unused_3866_ = lean_ctor_get(v_snd_3831_, 0);
lean_dec(v_unused_3866_);
v___x_3845_ = v_snd_3831_;
v_isShared_3846_ = v_isSharedCheck_3863_;
goto v_resetjp_3844_;
}
else
{
lean_dec(v_snd_3831_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3863_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v_a_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3852_; 
v_a_3847_ = lean_array_uget_borrowed(v_as_3824_, v_i_3826_);
v___x_3848_ = lean_array_fget(v_array_3836_, v_start_3837_);
v___x_3849_ = lean_unsigned_to_nat(1u);
v___x_3850_ = lean_nat_add(v_start_3837_, v___x_3849_);
lean_dec(v_start_3837_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 1, v___x_3850_);
v___x_3852_ = v___x_3845_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_array_3836_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3862_, 2, v_stop_3838_);
v___x_3852_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3853_; lean_object* v___x_3855_; 
v___x_3853_ = l_Lean_LocalDecl_fvarId(v_a_3847_);
lean_inc(v_a_3847_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 1, v___x_3848_);
lean_ctor_set(v___x_3834_, 0, v_a_3847_);
v___x_3855_ = v___x_3834_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3847_);
lean_ctor_set(v_reuseFailAlloc_3861_, 1, v___x_3848_);
v___x_3855_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; size_t v___x_3858_; size_t v___x_3859_; 
v___x_3856_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(v_fst_3832_, v___x_3853_, v___x_3855_);
v___x_3857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
lean_ctor_set(v___x_3857_, 1, v___x_3852_);
v___x_3858_ = ((size_t)1ULL);
v___x_3859_ = lean_usize_add(v_i_3826_, v___x_3858_);
v_i_3826_ = v___x_3859_;
v_b_3827_ = v___x_3857_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg___boxed(lean_object* v_as_3868_, lean_object* v_sz_3869_, lean_object* v_i_3870_, lean_object* v_b_3871_, lean_object* v___y_3872_){
_start:
{
size_t v_sz_boxed_3873_; size_t v_i_boxed_3874_; lean_object* v_res_3875_; 
v_sz_boxed_3873_ = lean_unbox_usize(v_sz_3869_);
lean_dec(v_sz_3869_);
v_i_boxed_3874_ = lean_unbox_usize(v_i_3870_);
lean_dec(v_i_3870_);
v_res_3875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_3868_, v_sz_boxed_3873_, v_i_boxed_3874_, v_b_3871_);
lean_dec_ref(v_as_3868_);
return v_res_3875_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2(void){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3878_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1));
v___x_3879_ = lean_unsigned_to_nat(2u);
v___x_3880_ = lean_unsigned_to_nat(372u);
v___x_3881_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3882_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3883_ = l_mkPanicMessageWithDecl(v___x_3882_, v___x_3881_, v___x_3880_, v___x_3879_, v___x_3878_);
return v___x_3883_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4(void){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3885_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3));
v___x_3886_ = lean_unsigned_to_nat(2u);
v___x_3887_ = lean_unsigned_to_nat(373u);
v___x_3888_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3889_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3890_ = l_mkPanicMessageWithDecl(v___x_3889_, v___x_3888_, v___x_3887_, v___x_3886_, v___x_3885_);
return v___x_3890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5(void){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3891_ = lean_box(0);
v___x_3892_ = lean_unsigned_to_nat(16u);
v___x_3893_ = lean_mk_array(v___x_3892_, v___x_3891_);
return v___x_3893_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3894_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5);
v___x_3895_ = lean_unsigned_to_nat(0u);
v___x_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
lean_ctor_set(v___x_3896_, 1, v___x_3894_);
return v___x_3896_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8(void){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7));
v___x_3899_ = l_Lean_stringToMessageData(v___x_3898_);
return v___x_3899_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9));
v___x_3902_ = l_Lean_stringToMessageData(v___x_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object* v_sortedDecls_3903_, lean_object* v_sortedArgs_3904_, lean_object* v_toSortDecls_3905_, lean_object* v_toSortArgs_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_){
_start:
{
lean_object* v___y_3911_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v_snd_3934_; lean_object* v___x_3936_; lean_object* v___x_3937_; uint8_t v___x_3938_; 
v___x_3936_ = lean_array_get_size(v_sortedDecls_3903_);
v___x_3937_ = lean_array_get_size(v_sortedArgs_3904_);
v___x_3938_ = lean_nat_dec_eq(v___x_3936_, v___x_3937_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
lean_dec_ref(v_toSortArgs_3906_);
lean_dec_ref(v_sortedArgs_3904_);
lean_dec_ref(v_sortedDecls_3903_);
v___x_3939_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2);
v___x_3940_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v___x_3939_, v_a_3907_, v_a_3908_);
return v___x_3940_;
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___x_3941_ = lean_array_get_size(v_toSortDecls_3905_);
v___x_3942_ = lean_array_get_size(v_toSortArgs_3906_);
v___x_3943_ = lean_nat_dec_eq(v___x_3941_, v___x_3942_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
lean_dec_ref(v_toSortArgs_3906_);
lean_dec_ref(v_sortedArgs_3904_);
lean_dec_ref(v_sortedDecls_3903_);
v___x_3944_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4);
v___x_3945_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v___x_3944_, v_a_3907_, v_a_3908_);
return v___x_3945_;
}
else
{
lean_object* v___x_3946_; uint8_t v___x_3947_; 
v___x_3946_ = lean_unsigned_to_nat(0u);
v___x_3947_ = lean_nat_dec_eq(v___x_3941_, v___x_3946_);
if (v___x_3947_ == 0)
{
lean_object* v_toCold_3948_; lean_object* v_options_3949_; lean_object* v_inheritedTraceOptions_3950_; uint8_t v_hasTrace_3951_; lean_object* v___x_3952_; lean_object* v_cls_3953_; lean_object* v___y_3955_; lean_object* v___y_3956_; 
v_toCold_3948_ = lean_ctor_get(v_a_3907_, 0);
v_options_3949_ = lean_ctor_get(v_toCold_3948_, 2);
v_inheritedTraceOptions_3950_ = lean_ctor_get(v_toCold_3948_, 11);
v_hasTrace_3951_ = lean_ctor_get_uint8(v_options_3949_, sizeof(void*)*1);
v___x_3952_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_cls_3953_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
if (v_hasTrace_3951_ == 0)
{
v___y_3955_ = v_a_3907_;
v___y_3956_ = v_a_3908_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_4057_; uint8_t v___x_4058_; 
v___x_4057_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4058_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3950_, v_options_3949_, v___x_4057_);
if (v___x_4058_ == 0)
{
v___y_3955_ = v_a_3907_;
v___y_3956_ = v_a_3908_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10);
v___x_4060_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3953_, v___x_4059_, v_a_3907_, v_a_3908_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_dec_ref_known(v___x_4060_, 1);
v___y_3955_ = v_a_3907_;
v___y_3956_ = v_a_3908_;
goto v___jp_3954_;
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec_ref(v_toSortArgs_3906_);
lean_dec_ref(v_sortedArgs_3904_);
lean_dec_ref(v_sortedDecls_3903_);
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4060_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4060_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
v___jp_3954_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; size_t v_sz_3960_; size_t v___x_3961_; lean_object* v___x_3962_; 
v___x_3957_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6);
v___x_3958_ = l_Array_toSubarray___redArg(v_sortedArgs_3904_, v___x_3946_, v___x_3937_);
v___x_3959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3957_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v_sz_3960_ = lean_array_size(v_sortedDecls_3903_);
v___x_3961_ = ((size_t)0ULL);
v___x_3962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_sortedDecls_3903_, v_sz_3960_, v___x_3961_, v___x_3959_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v_fst_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_4047_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3962_, 1);
v_fst_3964_ = lean_ctor_get(v_a_3963_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v_a_3963_);
if (v_isSharedCheck_4047_ == 0)
{
lean_object* v_unused_4048_; 
v_unused_4048_ = lean_ctor_get(v_a_3963_, 1);
lean_dec(v_unused_4048_);
v___x_3966_ = v_a_3963_;
v_isShared_3967_ = v_isSharedCheck_4047_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_fst_3964_);
lean_dec(v_a_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_4047_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3968_; lean_object* v___x_3970_; 
v___x_3968_ = l_Array_toSubarray___redArg(v_toSortArgs_3906_, v___x_3946_, v___x_3942_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 1, v___x_3968_);
v___x_3970_ = v___x_3966_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_fst_3964_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v___x_3968_);
v___x_3970_ = v_reuseFailAlloc_4046_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
size_t v_sz_3971_; lean_object* v___x_3972_; 
v_sz_3971_ = lean_array_size(v_toSortDecls_3905_);
v___x_3972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_toSortDecls_3905_, v_sz_3971_, v___x_3961_, v___x_3970_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v_fst_3974_; lean_object* v_size_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref_known(v___x_3972_, 1);
v_fst_3974_ = lean_ctor_get(v_a_3973_, 0);
lean_inc_n(v_fst_3974_, 2);
lean_dec(v_a_3973_);
v_size_3975_ = lean_ctor_get(v_fst_3974_, 0);
v___x_3976_ = lean_mk_empty_array_with_capacity(v_size_3975_);
lean_inc_ref(v___x_3976_);
v___x_3977_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3952_);
lean_ctor_set(v___x_3977_, 1, v___x_3952_);
lean_ctor_set(v___x_3977_, 2, v___x_3976_);
lean_ctor_set(v___x_3977_, 3, v___x_3976_);
v___x_3978_ = lean_box(0);
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3974_, v_sortedDecls_3903_, v_sz_3960_, v___x_3961_, v___x_3978_, v___x_3977_, v___y_3955_, v___y_3956_);
lean_dec_ref(v_sortedDecls_3903_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v_snd_3981_; lean_object* v___x_3982_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref_known(v___x_3979_, 1);
v_snd_3981_ = lean_ctor_get(v_a_3980_, 1);
lean_inc(v_snd_3981_);
lean_dec(v_a_3980_);
v___x_3982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_3974_, v_toSortDecls_3905_, v_sz_3971_, v___x_3961_, v___x_3978_, v_snd_3981_, v___y_3955_, v___y_3956_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v_snd_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4020_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref_known(v___x_3982_, 1);
v_snd_3984_ = lean_ctor_get(v_a_3983_, 1);
v_isSharedCheck_4020_ = !lean_is_exclusive(v_a_3983_);
if (v_isSharedCheck_4020_ == 0)
{
lean_object* v_unused_4021_; 
v_unused_4021_ = lean_ctor_get(v_a_3983_, 0);
lean_dec(v_unused_4021_);
v___x_3986_ = v_a_3983_;
v_isShared_3987_ = v_isSharedCheck_4020_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_snd_3984_);
lean_dec(v_a_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4020_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v_toCold_3988_; lean_object* v_options_3989_; lean_object* v_newDecls_3990_; lean_object* v_newArgs_3991_; lean_object* v_inheritedTraceOptions_3992_; uint8_t v_hasTrace_3993_; lean_object* v___f_3994_; 
v_toCold_3988_ = lean_ctor_get(v___y_3955_, 0);
v_options_3989_ = lean_ctor_get(v_toCold_3988_, 2);
v_newDecls_3990_ = lean_ctor_get(v_snd_3984_, 2);
v_newArgs_3991_ = lean_ctor_get(v_snd_3984_, 3);
v_inheritedTraceOptions_3992_ = lean_ctor_get(v_toCold_3988_, 11);
v_hasTrace_3993_ = lean_ctor_get_uint8(v_options_3989_, sizeof(void*)*1);
lean_inc_ref(v_newArgs_3991_);
lean_inc_ref(v_newDecls_3990_);
v___f_3994_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3994_, 0, v_newDecls_3990_);
lean_closure_set(v___f_3994_, 1, v_newArgs_3991_);
if (v_hasTrace_3993_ == 0)
{
lean_del_object(v___x_3986_);
v___y_3930_ = v___y_3956_;
v___y_3931_ = v___y_3955_;
v___y_3932_ = v___f_3994_;
v___y_3933_ = v___x_3978_;
v_snd_3934_ = v_snd_3984_;
goto v___jp_3929_;
}
else
{
lean_object* v___x_3995_; uint8_t v___x_3996_; 
v___x_3995_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_3996_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3992_, v_options_3989_, v___x_3995_);
if (v___x_3996_ == 0)
{
lean_del_object(v___x_3986_);
v___y_3930_ = v___y_3956_;
v___y_3931_ = v___y_3955_;
v___y_3932_ = v___f_3994_;
v___y_3933_ = v___x_3978_;
v_snd_3934_ = v_snd_3984_;
goto v___jp_3929_;
}
else
{
lean_object* v___x_3997_; size_t v_sz_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4005_; 
lean_inc_ref(v_newArgs_3991_);
lean_inc_ref_n(v_newDecls_3990_, 2);
lean_dec_ref(v___f_3994_);
v___x_3997_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8);
v_sz_3998_ = lean_array_size(v_newDecls_3990_);
v___x_3999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_3998_, v___x_3961_, v_newDecls_3990_);
v___x_4000_ = lean_array_to_list(v___x_3999_);
v___x_4001_ = lean_box(0);
v___x_4002_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v___x_4000_, v___x_4001_);
v___x_4003_ = l_Lean_MessageData_ofList(v___x_4002_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set_tag(v___x_3986_, 7);
lean_ctor_set(v___x_3986_, 1, v___x_4003_);
lean_ctor_set(v___x_3986_, 0, v___x_3997_);
v___x_4005_ = v___x_3986_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_3997_);
lean_ctor_set(v_reuseFailAlloc_4019_, 1, v___x_4003_);
v___x_4005_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3953_, v___x_4005_, v_snd_3984_, v___y_3955_, v___y_3956_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v_fst_4008_; lean_object* v_snd_4009_; lean_object* v___x_4010_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_4006_, 1);
v_fst_4008_ = lean_ctor_get(v_a_4007_, 0);
lean_inc(v_fst_4008_);
v_snd_4009_ = lean_ctor_get(v_a_4007_, 1);
lean_inc(v_snd_4009_);
lean_dec(v_a_4007_);
v___x_4010_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3990_, v_newArgs_3991_, v_fst_4008_, v_snd_4009_, v___y_3955_, v___y_3956_);
v___y_3911_ = v___x_4010_;
goto v___jp_3910_;
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec_ref(v_newArgs_3991_);
lean_dec_ref(v_newDecls_3990_);
v_a_4011_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_4006_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4006_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
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
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
v_a_4022_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_3982_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_3982_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
lean_dec(v_fst_3974_);
v_a_4030_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_3979_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_3979_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec_ref(v_sortedDecls_3903_);
v_a_4038_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_3972_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_3972_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec_ref(v_toSortArgs_3906_);
lean_dec_ref(v_sortedDecls_3903_);
v_a_4049_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_3962_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_3962_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
}
else
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
lean_dec_ref(v_toSortArgs_3906_);
v___x_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4069_, 0, v_sortedDecls_3903_);
lean_ctor_set(v___x_4069_, 1, v_sortedArgs_3904_);
v___x_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4069_);
return v___x_4070_;
}
}
}
v___jp_3910_:
{
if (lean_obj_tag(v___y_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3920_; 
v_a_3912_ = lean_ctor_get(v___y_3911_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___y_3911_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3914_ = v___y_3911_;
v_isShared_3915_ = v_isSharedCheck_3920_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___y_3911_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3920_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v_fst_3916_; lean_object* v___x_3918_; 
v_fst_3916_ = lean_ctor_get(v_a_3912_, 0);
lean_inc(v_fst_3916_);
lean_dec(v_a_3912_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v_fst_3916_);
v___x_3918_ = v___x_3914_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_fst_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
v_a_3921_ = lean_ctor_get(v___y_3911_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___y_3911_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___y_3911_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___y_3911_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
v___jp_3929_:
{
lean_object* v___x_3935_; 
lean_inc(v___y_3930_);
lean_inc_ref(v___y_3931_);
v___x_3935_ = lean_apply_5(v___y_3932_, v___y_3933_, v_snd_3934_, v___y_3931_, v___y_3930_, lean_box(0));
v___y_3911_ = v___x_3935_;
goto v___jp_3910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object* v_sortedDecls_4071_, lean_object* v_sortedArgs_4072_, lean_object* v_toSortDecls_4073_, lean_object* v_toSortArgs_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v_sortedDecls_4071_, v_sortedArgs_4072_, v_toSortDecls_4073_, v_toSortArgs_4074_, v_a_4075_, v_a_4076_);
lean_dec(v_a_4076_);
lean_dec_ref(v_a_4075_);
lean_dec_ref(v_toSortDecls_4073_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object* v_00_u03b2_4079_, lean_object* v_m_4080_, lean_object* v_a_4081_, lean_object* v_b_4082_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(v_m_4080_, v_a_4081_, v_b_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object* v_as_4084_, size_t v_sz_4085_, size_t v_i_4086_, lean_object* v_b_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_4084_, v_sz_4085_, v_i_4086_, v_b_4087_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object* v_as_4092_, lean_object* v_sz_4093_, lean_object* v_i_4094_, lean_object* v_b_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
size_t v_sz_boxed_4099_; size_t v_i_boxed_4100_; lean_object* v_res_4101_; 
v_sz_boxed_4099_ = lean_unbox_usize(v_sz_4093_);
lean_dec(v_sz_4093_);
v_i_boxed_4100_ = lean_unbox_usize(v_i_4094_);
lean_dec(v_i_4094_);
v_res_4101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_as_4092_, v_sz_boxed_4099_, v_i_boxed_4100_, v_b_4095_, v___y_4096_, v___y_4097_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec_ref(v_as_4092_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0(lean_object* v_00_u03b2_4102_, lean_object* v_a_4103_, lean_object* v_b_4104_, lean_object* v_x_4105_){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_4103_, v_b_4104_, v_x_4105_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(lean_object* v_msg_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___f_4114_; lean_object* v___x_1735__overap_4115_; lean_object* v___x_4116_; 
v___f_4114_ = ((lean_object*)(l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1___closed__0));
v___x_1735__overap_4115_ = lean_panic_fn_borrowed(v___f_4114_, v_msg_4108_);
lean_inc(v___y_4112_);
lean_inc_ref(v___y_4111_);
lean_inc(v___y_4110_);
lean_inc_ref(v___y_4109_);
v___x_4116_ = lean_apply_5(v___x_1735__overap_4115_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, lean_box(0));
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1___boxed(lean_object* v_msg_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(v_msg_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
return v_res_4123_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(lean_object* v_as_4124_, size_t v_i_4125_, size_t v_stop_4126_){
_start:
{
uint8_t v___x_4131_; 
v___x_4131_ = lean_usize_dec_eq(v_i_4125_, v_stop_4126_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4132_; 
v___x_4132_ = lean_array_uget_borrowed(v_as_4124_, v_i_4125_);
if (lean_obj_tag(v___x_4132_) == 0)
{
goto v___jp_4127_;
}
else
{
lean_object* v_val_4133_; uint8_t v___x_4134_; 
v_val_4133_ = lean_ctor_get(v___x_4132_, 0);
v___x_4134_ = l_Lean_LocalDecl_isLet(v_val_4133_, v___x_4131_);
if (v___x_4134_ == 0)
{
goto v___jp_4127_;
}
else
{
return v___x_4134_;
}
}
}
else
{
uint8_t v___x_4135_; 
v___x_4135_ = 0;
return v___x_4135_;
}
v___jp_4127_:
{
size_t v___x_4128_; size_t v___x_4129_; 
v___x_4128_ = ((size_t)1ULL);
v___x_4129_ = lean_usize_add(v_i_4125_, v___x_4128_);
v_i_4125_ = v___x_4129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1___boxed(lean_object* v_as_4136_, lean_object* v_i_4137_, lean_object* v_stop_4138_){
_start:
{
size_t v_i_boxed_4139_; size_t v_stop_boxed_4140_; uint8_t v_res_4141_; lean_object* v_r_4142_; 
v_i_boxed_4139_ = lean_unbox_usize(v_i_4137_);
lean_dec(v_i_4137_);
v_stop_boxed_4140_ = lean_unbox_usize(v_stop_4138_);
lean_dec(v_stop_4138_);
v_res_4141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_as_4136_, v_i_boxed_4139_, v_stop_boxed_4140_);
lean_dec_ref(v_as_4136_);
v_r_4142_ = lean_box(v_res_4141_);
return v_r_4142_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(lean_object* v_x_4143_){
_start:
{
if (lean_obj_tag(v_x_4143_) == 0)
{
lean_object* v_cs_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; uint8_t v___x_4147_; 
v_cs_4144_ = lean_ctor_get(v_x_4143_, 0);
v___x_4145_ = lean_unsigned_to_nat(0u);
v___x_4146_ = lean_array_get_size(v_cs_4144_);
v___x_4147_ = lean_nat_dec_lt(v___x_4145_, v___x_4146_);
if (v___x_4147_ == 0)
{
return v___x_4147_;
}
else
{
size_t v___x_4148_; size_t v___x_4149_; uint8_t v___x_4150_; 
v___x_4148_ = ((size_t)0ULL);
v___x_4149_ = lean_usize_of_nat(v___x_4146_);
v___x_4150_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(v_cs_4144_, v___x_4148_, v___x_4149_);
return v___x_4150_;
}
}
else
{
lean_object* v_vs_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; uint8_t v___x_4154_; 
v_vs_4151_ = lean_ctor_get(v_x_4143_, 0);
v___x_4152_ = lean_unsigned_to_nat(0u);
v___x_4153_ = lean_array_get_size(v_vs_4151_);
v___x_4154_ = lean_nat_dec_lt(v___x_4152_, v___x_4153_);
if (v___x_4154_ == 0)
{
return v___x_4154_;
}
else
{
size_t v___x_4155_; size_t v___x_4156_; uint8_t v___x_4157_; 
v___x_4155_ = ((size_t)0ULL);
v___x_4156_ = lean_usize_of_nat(v___x_4153_);
v___x_4157_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_vs_4151_, v___x_4155_, v___x_4156_);
return v___x_4157_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(lean_object* v_as_4158_, size_t v_i_4159_, size_t v_stop_4160_){
_start:
{
uint8_t v___x_4161_; 
v___x_4161_ = lean_usize_dec_eq(v_i_4159_, v_stop_4160_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4162_; uint8_t v___x_4163_; 
v___x_4162_ = lean_array_uget_borrowed(v_as_4158_, v_i_4159_);
v___x_4163_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v___x_4162_);
if (v___x_4163_ == 0)
{
size_t v___x_4164_; size_t v___x_4165_; 
v___x_4164_ = ((size_t)1ULL);
v___x_4165_ = lean_usize_add(v_i_4159_, v___x_4164_);
v_i_4159_ = v___x_4165_;
goto _start;
}
else
{
return v___x_4163_;
}
}
else
{
uint8_t v___x_4167_; 
v___x_4167_ = 0;
return v___x_4167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4168_, lean_object* v_i_4169_, lean_object* v_stop_4170_){
_start:
{
size_t v_i_boxed_4171_; size_t v_stop_boxed_4172_; uint8_t v_res_4173_; lean_object* v_r_4174_; 
v_i_boxed_4171_ = lean_unbox_usize(v_i_4169_);
lean_dec(v_i_4169_);
v_stop_boxed_4172_ = lean_unbox_usize(v_stop_4170_);
lean_dec(v_stop_4170_);
v_res_4173_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(v_as_4168_, v_i_boxed_4171_, v_stop_boxed_4172_);
lean_dec_ref(v_as_4168_);
v_r_4174_ = lean_box(v_res_4173_);
return v_r_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0___boxed(lean_object* v_x_4175_){
_start:
{
uint8_t v_res_4176_; lean_object* v_r_4177_; 
v_res_4176_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v_x_4175_);
lean_dec_ref(v_x_4175_);
v_r_4177_ = lean_box(v_res_4176_);
return v_r_4177_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object* v_t_4178_){
_start:
{
lean_object* v_root_4179_; lean_object* v_tail_4180_; uint8_t v___x_4181_; 
v_root_4179_ = lean_ctor_get(v_t_4178_, 0);
v_tail_4180_ = lean_ctor_get(v_t_4178_, 1);
v___x_4181_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v_root_4179_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4182_; lean_object* v___x_4183_; uint8_t v___x_4184_; 
v___x_4182_ = lean_unsigned_to_nat(0u);
v___x_4183_ = lean_array_get_size(v_tail_4180_);
v___x_4184_ = lean_nat_dec_lt(v___x_4182_, v___x_4183_);
if (v___x_4184_ == 0)
{
return v___x_4184_;
}
else
{
size_t v___x_4185_; size_t v___x_4186_; uint8_t v___x_4187_; 
v___x_4185_ = ((size_t)0ULL);
v___x_4186_ = lean_usize_of_nat(v___x_4183_);
v___x_4187_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_tail_4180_, v___x_4185_, v___x_4186_);
return v___x_4187_;
}
}
else
{
return v___x_4181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object* v_t_4188_){
_start:
{
uint8_t v_res_4189_; lean_object* v_r_4190_; 
v_res_4189_ = l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_t_4188_);
lean_dec_ref(v_t_4188_);
v_r_4190_ = lean_box(v_res_4189_);
return v_r_4190_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0(void){
_start:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4191_ = lean_box(0);
v___x_4192_ = lean_unsigned_to_nat(16u);
v___x_4193_ = lean_mk_array(v___x_4192_, v___x_4191_);
return v___x_4193_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1(void){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4194_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0);
v___x_4195_ = lean_unsigned_to_nat(0u);
v___x_4196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
lean_ctor_set(v___x_4196_, 1, v___x_4194_);
return v___x_4196_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4199_ = lean_unsigned_to_nat(1u);
v___x_4200_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2));
v___x_4201_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
v___x_4202_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
lean_ctor_set(v___x_4202_, 2, v___x_4200_);
lean_ctor_set(v___x_4202_, 3, v___x_4199_);
lean_ctor_set(v___x_4202_, 4, v___x_4200_);
lean_ctor_set(v___x_4202_, 5, v___x_4200_);
lean_ctor_set(v___x_4202_, 6, v___x_4200_);
lean_ctor_set(v___x_4202_, 7, v___x_4200_);
lean_ctor_set(v___x_4202_, 8, v___x_4199_);
lean_ctor_set(v___x_4202_, 9, v___x_4200_);
lean_ctor_set(v___x_4202_, 10, v___x_4200_);
lean_ctor_set(v___x_4202_, 11, v___x_4200_);
return v___x_4202_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4205_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5));
v___x_4206_ = lean_unsigned_to_nat(2u);
v___x_4207_ = lean_unsigned_to_nat(424u);
v___x_4208_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__4));
v___x_4209_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_4210_ = l_mkPanicMessageWithDecl(v___x_4209_, v___x_4208_, v___x_4207_, v___x_4206_, v___x_4205_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* v_type_4211_, lean_object* v_value_4212_, uint8_t v_zetaDelta_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_){
_start:
{
lean_object* v_lctx_4219_; lean_object* v_decls_4220_; uint8_t v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v_lctx_4219_ = lean_ctor_get(v_a_4214_, 2);
v_decls_4220_ = lean_ctor_get(v_lctx_4219_, 1);
v___x_4221_ = l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_decls_4220_);
v___x_4222_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4222_, 0, v_zetaDelta_4213_);
lean_ctor_set_uint8(v___x_4222_, 1, v___x_4221_);
v___x_4223_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__3, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3);
v___x_4224_ = lean_st_mk_ref(v___x_4223_);
v___x_4225_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_4211_, v_value_4212_, v___x_4222_, v___x_4224_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_);
lean_dec_ref_known(v___x_4222_, 0);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4227_; lean_object* v_fst_4228_; lean_object* v_snd_4229_; lean_object* v_levelParams_4230_; lean_object* v_levelArgs_4231_; lean_object* v_newLocalDecls_4232_; lean_object* v_newLocalDeclsForMVars_4233_; lean_object* v_newLetDecls_4234_; lean_object* v_exprMVarArgs_4235_; lean_object* v_exprFVarArgs_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
v___x_4227_ = lean_st_ref_get(v___x_4224_);
lean_dec(v___x_4224_);
v_fst_4228_ = lean_ctor_get(v_a_4226_, 0);
lean_inc(v_fst_4228_);
v_snd_4229_ = lean_ctor_get(v_a_4226_, 1);
lean_inc(v_snd_4229_);
lean_dec(v_a_4226_);
v_levelParams_4230_ = lean_ctor_get(v___x_4227_, 2);
lean_inc_ref(v_levelParams_4230_);
v_levelArgs_4231_ = lean_ctor_get(v___x_4227_, 4);
lean_inc_ref(v_levelArgs_4231_);
v_newLocalDecls_4232_ = lean_ctor_get(v___x_4227_, 5);
lean_inc_ref(v_newLocalDecls_4232_);
v_newLocalDeclsForMVars_4233_ = lean_ctor_get(v___x_4227_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_4233_);
v_newLetDecls_4234_ = lean_ctor_get(v___x_4227_, 7);
lean_inc_ref(v_newLetDecls_4234_);
v_exprMVarArgs_4235_ = lean_ctor_get(v___x_4227_, 9);
lean_inc_ref(v_exprMVarArgs_4235_);
v_exprFVarArgs_4236_ = lean_ctor_get(v___x_4227_, 10);
lean_inc_ref(v_exprFVarArgs_4236_);
lean_dec(v___x_4227_);
v___x_4237_ = l_Array_reverse___redArg(v_newLocalDecls_4232_);
v___x_4238_ = l_Array_reverse___redArg(v_exprFVarArgs_4236_);
v___x_4239_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v___x_4237_, v___x_4238_, v_newLocalDeclsForMVars_4233_, v_exprMVarArgs_4235_, v_a_4216_, v_a_4217_);
lean_dec_ref(v_newLocalDeclsForMVars_4233_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4258_; 
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4242_ = v___x_4239_;
v_isShared_4243_ = v_isSharedCheck_4258_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4239_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4258_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v_fst_4244_; lean_object* v_snd_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; uint8_t v___x_4251_; 
v_fst_4244_ = lean_ctor_get(v_a_4240_, 0);
lean_inc_n(v_fst_4244_, 2);
v_snd_4245_ = lean_ctor_get(v_a_4240_, 1);
lean_inc(v_snd_4245_);
lean_dec(v_a_4240_);
v___x_4246_ = l_Array_reverse___redArg(v_newLetDecls_4234_);
lean_inc_ref(v___x_4246_);
v___x_4247_ = l_Lean_Meta_Closure_mkForall(v___x_4246_, v_fst_4228_);
lean_dec(v_fst_4228_);
v___x_4248_ = l_Lean_Meta_Closure_mkForall(v_fst_4244_, v___x_4247_);
lean_dec_ref(v___x_4247_);
v___x_4249_ = l_Lean_Meta_Closure_mkLambda(v___x_4246_, v_snd_4229_);
lean_dec(v_snd_4229_);
v___x_4250_ = l_Lean_Meta_Closure_mkLambda(v_fst_4244_, v___x_4249_);
lean_dec_ref(v___x_4249_);
v___x_4251_ = l_Lean_Expr_hasFVar(v___x_4250_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4252_; lean_object* v___x_4254_; 
v___x_4252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4252_, 0, v_levelParams_4230_);
lean_ctor_set(v___x_4252_, 1, v___x_4248_);
lean_ctor_set(v___x_4252_, 2, v___x_4250_);
lean_ctor_set(v___x_4252_, 3, v_levelArgs_4231_);
lean_ctor_set(v___x_4252_, 4, v_snd_4245_);
if (v_isShared_4243_ == 0)
{
lean_ctor_set(v___x_4242_, 0, v___x_4252_);
v___x_4254_ = v___x_4242_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4252_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
else
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
lean_dec_ref(v___x_4250_);
lean_dec_ref(v___x_4248_);
lean_dec(v_snd_4245_);
lean_del_object(v___x_4242_);
lean_dec_ref(v_levelArgs_4231_);
lean_dec_ref(v_levelParams_4230_);
v___x_4256_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__6, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6);
v___x_4257_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(v___x_4256_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_);
return v___x_4257_;
}
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
lean_dec_ref(v_newLetDecls_4234_);
lean_dec_ref(v_levelArgs_4231_);
lean_dec_ref(v_levelParams_4230_);
lean_dec(v_snd_4229_);
lean_dec(v_fst_4228_);
v_a_4259_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4239_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4239_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
else
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
lean_dec(v___x_4224_);
v_a_4267_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4225_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4225_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* v_type_4275_, lean_object* v_value_4276_, lean_object* v_zetaDelta_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_){
_start:
{
uint8_t v_zetaDelta_boxed_4283_; lean_object* v_res_4284_; 
v_zetaDelta_boxed_4283_ = lean_unbox(v_zetaDelta_4277_);
v_res_4284_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4275_, v_value_4276_, v_zetaDelta_boxed_4283_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* v_name_4285_, lean_object* v_levelParams_4286_, lean_object* v_type_4287_, lean_object* v_value_4288_, lean_object* v_hints_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v___x_4292_; uint8_t v___y_4294_; lean_object* v_env_4302_; uint8_t v___x_4303_; 
v___x_4292_ = lean_st_ref_get(v___y_4290_);
v_env_4302_ = lean_ctor_get(v___x_4292_, 0);
lean_inc_ref_n(v_env_4302_, 2);
lean_dec(v___x_4292_);
v___x_4303_ = l_Lean_Environment_hasUnsafe(v_env_4302_, v_type_4287_);
if (v___x_4303_ == 0)
{
uint8_t v___x_4304_; 
v___x_4304_ = l_Lean_Environment_hasUnsafe(v_env_4302_, v_value_4288_);
if (v___x_4304_ == 0)
{
uint8_t v___x_4305_; 
v___x_4305_ = 1;
v___y_4294_ = v___x_4305_;
goto v___jp_4293_;
}
else
{
goto v___jp_4300_;
}
}
else
{
lean_dec_ref(v_env_4302_);
goto v___jp_4300_;
}
v___jp_4293_:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
lean_inc(v_name_4285_);
v___x_4295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4295_, 0, v_name_4285_);
lean_ctor_set(v___x_4295_, 1, v_levelParams_4286_);
lean_ctor_set(v___x_4295_, 2, v_type_4287_);
v___x_4296_ = lean_box(0);
v___x_4297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4297_, 0, v_name_4285_);
lean_ctor_set(v___x_4297_, 1, v___x_4296_);
v___x_4298_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4298_, 0, v___x_4295_);
lean_ctor_set(v___x_4298_, 1, v_value_4288_);
lean_ctor_set(v___x_4298_, 2, v_hints_4289_);
lean_ctor_set(v___x_4298_, 3, v___x_4297_);
lean_ctor_set_uint8(v___x_4298_, sizeof(void*)*4, v___y_4294_);
v___x_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
return v___x_4299_;
}
v___jp_4300_:
{
uint8_t v___x_4301_; 
v___x_4301_ = 0;
v___y_4294_ = v___x_4301_;
goto v___jp_4293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* v_name_4306_, lean_object* v_levelParams_4307_, lean_object* v_type_4308_, lean_object* v_value_4309_, lean_object* v_hints_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4306_, v_levelParams_4307_, v_type_4308_, v_value_4309_, v_hints_4310_, v___y_4311_);
lean_dec(v___y_4311_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(lean_object* v_name_4314_, lean_object* v_levelParams_4315_, lean_object* v_type_4316_, lean_object* v_value_4317_, lean_object* v_hints_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4314_, v_levelParams_4315_, v_type_4316_, v_value_4317_, v_hints_4318_, v___y_4322_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* v_name_4325_, lean_object* v_levelParams_4326_, lean_object* v_type_4327_, lean_object* v_value_4328_, lean_object* v_hints_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(v_name_4325_, v_levelParams_4326_, v_type_4327_, v_value_4328_, v_hints_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* v_name_4336_, lean_object* v_type_4337_, lean_object* v_value_4338_, uint8_t v_zetaDelta_4339_, uint8_t v_compile_4340_, uint8_t v_logCompileErrors_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v___x_4347_; 
v___x_4347_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4337_, v_value_4338_, v_zetaDelta_4339_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4399_; 
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4350_ = v___x_4347_;
v_isShared_4351_ = v_isSharedCheck_4399_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4347_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4399_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4361_; lean_object* v_env_4362_; lean_object* v_levelParams_4363_; lean_object* v_type_4364_; lean_object* v_value_4365_; uint32_t v___x_4366_; uint32_t v___x_4367_; uint32_t v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4398_; 
v___x_4361_ = lean_st_ref_get(v_a_4345_);
v_env_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc_ref(v_env_4362_);
lean_dec(v___x_4361_);
v_levelParams_4363_ = lean_ctor_get(v_a_4348_, 0);
v_type_4364_ = lean_ctor_get(v_a_4348_, 1);
v_value_4365_ = lean_ctor_get(v_a_4348_, 2);
lean_inc_ref_n(v_value_4365_, 2);
v___x_4366_ = l_Lean_getMaxHeight(v_env_4362_, v_value_4365_);
v___x_4367_ = 1;
v___x_4368_ = lean_uint32_add(v___x_4366_, v___x_4367_);
v___x_4369_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4369_, 0, v___x_4368_);
lean_inc_ref(v_levelParams_4363_);
v___x_4370_ = lean_array_to_list(v_levelParams_4363_);
lean_inc_ref(v_type_4364_);
lean_inc(v_name_4336_);
v___x_4371_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4336_, v___x_4370_, v_type_4364_, v_value_4365_, v___x_4369_, v_a_4345_);
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4374_ = v___x_4371_;
v_isShared_4375_ = v_isSharedCheck_4398_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4371_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4398_;
goto v_resetjp_4373_;
}
v___jp_4352_:
{
lean_object* v_levelArgs_4353_; lean_object* v_exprArgs_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4359_; 
v_levelArgs_4353_ = lean_ctor_get(v_a_4348_, 3);
lean_inc_ref(v_levelArgs_4353_);
v_exprArgs_4354_ = lean_ctor_get(v_a_4348_, 4);
lean_inc_ref(v_exprArgs_4354_);
lean_dec(v_a_4348_);
v___x_4355_ = lean_array_to_list(v_levelArgs_4353_);
v___x_4356_ = l_Lean_mkConst(v_name_4336_, v___x_4355_);
v___x_4357_ = l_Lean_mkAppN(v___x_4356_, v_exprArgs_4354_);
lean_dec_ref(v_exprArgs_4354_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 0, v___x_4357_);
v___x_4359_ = v___x_4350_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4357_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
lean_ctor_set_tag(v___x_4374_, 1);
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
uint8_t v___x_4378_; lean_object* v___x_4379_; 
v___x_4378_ = 0;
lean_inc_ref(v___x_4377_);
v___x_4379_ = l_Lean_addDecl(v___x_4377_, v___x_4378_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_dec_ref_known(v___x_4379_, 1);
if (v_compile_4340_ == 0)
{
lean_dec_ref(v___x_4377_);
goto v___jp_4352_;
}
else
{
lean_object* v___x_4380_; 
v___x_4380_ = l_Lean_compileDecl(v___x_4377_, v_logCompileErrors_4341_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_dec_ref_known(v___x_4380_, 1);
goto v___jp_4352_;
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_del_object(v___x_4350_);
lean_dec(v_a_4348_);
lean_dec(v_name_4336_);
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4380_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4380_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec_ref(v___x_4377_);
lean_del_object(v___x_4350_);
lean_dec(v_a_4348_);
lean_dec(v_name_4336_);
v_a_4389_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4379_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4379_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_dec(v_name_4336_);
v_a_4400_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4347_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4347_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* v_name_4408_, lean_object* v_type_4409_, lean_object* v_value_4410_, lean_object* v_zetaDelta_4411_, lean_object* v_compile_4412_, lean_object* v_logCompileErrors_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_){
_start:
{
uint8_t v_zetaDelta_boxed_4419_; uint8_t v_compile_boxed_4420_; uint8_t v_logCompileErrors_boxed_4421_; lean_object* v_res_4422_; 
v_zetaDelta_boxed_4419_ = lean_unbox(v_zetaDelta_4411_);
v_compile_boxed_4420_ = lean_unbox(v_compile_4412_);
v_logCompileErrors_boxed_4421_ = lean_unbox(v_logCompileErrors_4413_);
v_res_4422_ = l_Lean_Meta_mkAuxDefinition(v_name_4408_, v_type_4409_, v_value_4410_, v_zetaDelta_boxed_4419_, v_compile_boxed_4420_, v_logCompileErrors_boxed_4421_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
lean_dec(v_a_4417_);
lean_dec_ref(v_a_4416_);
lean_dec(v_a_4415_);
lean_dec_ref(v_a_4414_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* v_name_4423_, lean_object* v_value_4424_, uint8_t v_zetaDelta_4425_, uint8_t v_compile_4426_, uint8_t v_logCompileErrors_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
lean_object* v___x_4433_; 
lean_inc(v_a_4431_);
lean_inc_ref(v_a_4430_);
lean_inc(v_a_4429_);
lean_inc_ref(v_a_4428_);
lean_inc_ref(v_value_4424_);
v___x_4433_ = lean_infer_type(v_value_4424_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4434_);
lean_dec_ref_known(v___x_4433_, 1);
v___x_4435_ = l_Lean_Expr_headBeta(v_a_4434_);
v___x_4436_ = l_Lean_Meta_mkAuxDefinition(v_name_4423_, v___x_4435_, v_value_4424_, v_zetaDelta_4425_, v_compile_4426_, v_logCompileErrors_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_);
return v___x_4436_;
}
else
{
lean_dec_ref(v_value_4424_);
lean_dec(v_name_4423_);
return v___x_4433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* v_name_4437_, lean_object* v_value_4438_, lean_object* v_zetaDelta_4439_, lean_object* v_compile_4440_, lean_object* v_logCompileErrors_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_){
_start:
{
uint8_t v_zetaDelta_boxed_4447_; uint8_t v_compile_boxed_4448_; uint8_t v_logCompileErrors_boxed_4449_; lean_object* v_res_4450_; 
v_zetaDelta_boxed_4447_ = lean_unbox(v_zetaDelta_4439_);
v_compile_boxed_4448_ = lean_unbox(v_compile_4440_);
v_logCompileErrors_boxed_4449_ = lean_unbox(v_logCompileErrors_4441_);
v_res_4450_ = l_Lean_Meta_mkAuxDefinitionFor(v_name_4437_, v_value_4438_, v_zetaDelta_boxed_4447_, v_compile_boxed_4448_, v_logCompileErrors_boxed_4449_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_);
lean_dec(v_a_4445_);
lean_dec_ref(v_a_4444_);
lean_dec(v_a_4443_);
lean_dec_ref(v_a_4442_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* v_type_4451_, lean_object* v_value_4452_, uint8_t v_zetaDelta_4453_, lean_object* v_kind_x3f_4454_, uint8_t v_cache_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_){
_start:
{
lean_object* v___x_4461_; 
v___x_4461_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4451_, v_value_4452_, v_zetaDelta_4453_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_a_4462_; lean_object* v_levelParams_4463_; lean_object* v_type_4464_; lean_object* v_value_4465_; lean_object* v_levelArgs_4466_; lean_object* v_exprArgs_4467_; lean_object* v___x_4468_; uint8_t v___x_4469_; lean_object* v___x_4470_; 
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_a_4462_);
lean_dec_ref_known(v___x_4461_, 1);
v_levelParams_4463_ = lean_ctor_get(v_a_4462_, 0);
lean_inc_ref(v_levelParams_4463_);
v_type_4464_ = lean_ctor_get(v_a_4462_, 1);
lean_inc_ref(v_type_4464_);
v_value_4465_ = lean_ctor_get(v_a_4462_, 2);
lean_inc_ref(v_value_4465_);
v_levelArgs_4466_ = lean_ctor_get(v_a_4462_, 3);
lean_inc_ref(v_levelArgs_4466_);
v_exprArgs_4467_ = lean_ctor_get(v_a_4462_, 4);
lean_inc_ref(v_exprArgs_4467_);
lean_dec(v_a_4462_);
v___x_4468_ = lean_array_to_list(v_levelParams_4463_);
v___x_4469_ = 0;
v___x_4470_ = l_Lean_Meta_mkAuxLemma(v___x_4468_, v_type_4464_, v_value_4465_, v_kind_x3f_4454_, v_cache_4455_, v___x_4469_, v___x_4469_, v___x_4469_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4481_; 
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4473_ = v___x_4470_;
v_isShared_4474_ = v_isSharedCheck_4481_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4470_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4481_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4479_; 
v___x_4475_ = lean_array_to_list(v_levelArgs_4466_);
v___x_4476_ = l_Lean_mkConst(v_a_4471_, v___x_4475_);
v___x_4477_ = l_Lean_mkAppN(v___x_4476_, v_exprArgs_4467_);
lean_dec_ref(v_exprArgs_4467_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 0, v___x_4477_);
v___x_4479_ = v___x_4473_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
else
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4489_; 
lean_dec_ref(v_exprArgs_4467_);
lean_dec_ref(v_levelArgs_4466_);
v_a_4482_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4484_ = v___x_4470_;
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4470_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4482_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
lean_dec(v_kind_x3f_4454_);
v_a_4490_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4461_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4461_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* v_type_4498_, lean_object* v_value_4499_, lean_object* v_zetaDelta_4500_, lean_object* v_kind_x3f_4501_, lean_object* v_cache_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_){
_start:
{
uint8_t v_zetaDelta_boxed_4508_; uint8_t v_cache_boxed_4509_; lean_object* v_res_4510_; 
v_zetaDelta_boxed_4508_ = lean_unbox(v_zetaDelta_4500_);
v_cache_boxed_4509_ = lean_unbox(v_cache_4502_);
v_res_4510_ = l_Lean_Meta_mkAuxTheorem(v_type_4498_, v_value_4499_, v_zetaDelta_boxed_4508_, v_kind_x3f_4501_, v_cache_boxed_4509_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4566_; uint8_t v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4566_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_4567_ = 0;
v___x_4568_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_));
v___x_4569_ = l_Lean_registerTraceClass(v___x_4566_, v___x_4567_, v___x_4568_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
return v_res_4571_;
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
