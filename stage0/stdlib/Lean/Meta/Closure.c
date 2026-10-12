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
lean_object* l_Lean_Meta_Closure_visitLevel(lean_object* v_f_7_, lean_object* v_u_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
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
LEAN_EXPORT void l_Lean_Meta_Closure_visitLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_7_ = stack[0].m_obj;
lean_object* v_u_8_ = stack[1].m_obj;
lean_object* v_a_9_ = stack[2].m_obj;
lean_object* v_a_10_ = stack[3].m_obj;
lean_object* v_a_11_ = stack[4].m_obj;
lean_object* v_a_12_ = stack[5].m_obj;
lean_object* v_a_13_ = stack[6].m_obj;
lean_object* v_a_14_ = stack[7].m_obj;
lean_object* v_res_64_;
v_res_64_ = l_Lean_Meta_Closure_visitLevel(v_f_7_, v_u_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitLevel___boxed(lean_object* v_f_65_, lean_object* v_u_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Meta_Closure_visitLevel(v_f_65_, v_u_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
return v_res_74_;
}
}
lean_object* l_Lean_Meta_Closure_visitExpr(lean_object* v_f_77_, lean_object* v_e_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_131_; 
v___x_86_ = ((lean_object*)(l_Lean_Meta_Closure_visitExpr___closed__0));
v___x_87_ = ((lean_object*)(l_Lean_Meta_Closure_visitExpr___closed__1));
v___x_131_ = l_Lean_Expr_hasLevelParam(v_e_78_);
if (v___x_131_ == 0)
{
uint8_t v___x_132_; 
v___x_132_ = l_Lean_Expr_hasFVar(v_e_78_);
if (v___x_132_ == 0)
{
uint8_t v___x_133_; 
v___x_133_ = l_Lean_Expr_hasMVar(v_e_78_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
lean_dec_ref(v_f_77_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v_e_78_);
return v___x_134_;
}
else
{
goto v___jp_88_;
}
}
else
{
goto v___jp_88_;
}
}
else
{
goto v___jp_88_;
}
v___jp_88_:
{
lean_object* v___x_89_; lean_object* v_visitedExpr_90_; lean_object* v___x_91_; 
v___x_89_ = lean_st_ref_get(v_a_80_);
v_visitedExpr_90_ = lean_ctor_get(v___x_89_, 1);
lean_inc_ref(v_visitedExpr_90_);
lean_dec(v___x_89_);
lean_inc_ref(v_e_78_);
v___x_91_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_86_, v___x_87_, v_visitedExpr_90_, v_e_78_);
lean_dec_ref(v_visitedExpr_90_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v___x_92_; 
lean_inc(v_a_84_);
lean_inc_ref(v_a_83_);
lean_inc(v_a_82_);
lean_inc_ref(v_a_81_);
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc_ref(v_e_78_);
v___x_92_ = lean_apply_8(v_f_77_, v_e_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, lean_box(0));
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_122_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_122_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_122_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_122_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v_visitedLevel_98_; lean_object* v_visitedExpr_99_; lean_object* v_levelParams_100_; lean_object* v_nextLevelIdx_101_; lean_object* v_levelArgs_102_; lean_object* v_newLocalDecls_103_; lean_object* v_newLocalDeclsForMVars_104_; lean_object* v_newLetDecls_105_; lean_object* v_nextExprIdx_106_; lean_object* v_exprMVarArgs_107_; lean_object* v_exprFVarArgs_108_; lean_object* v_toProcess_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_121_; 
v___x_97_ = lean_st_ref_take(v_a_80_);
v_visitedLevel_98_ = lean_ctor_get(v___x_97_, 0);
v_visitedExpr_99_ = lean_ctor_get(v___x_97_, 1);
v_levelParams_100_ = lean_ctor_get(v___x_97_, 2);
v_nextLevelIdx_101_ = lean_ctor_get(v___x_97_, 3);
v_levelArgs_102_ = lean_ctor_get(v___x_97_, 4);
v_newLocalDecls_103_ = lean_ctor_get(v___x_97_, 5);
v_newLocalDeclsForMVars_104_ = lean_ctor_get(v___x_97_, 6);
v_newLetDecls_105_ = lean_ctor_get(v___x_97_, 7);
v_nextExprIdx_106_ = lean_ctor_get(v___x_97_, 8);
v_exprMVarArgs_107_ = lean_ctor_get(v___x_97_, 9);
v_exprFVarArgs_108_ = lean_ctor_get(v___x_97_, 10);
v_toProcess_109_ = lean_ctor_get(v___x_97_, 11);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_121_ == 0)
{
v___x_111_ = v___x_97_;
v_isShared_112_ = v_isSharedCheck_121_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_toProcess_109_);
lean_inc(v_exprFVarArgs_108_);
lean_inc(v_exprMVarArgs_107_);
lean_inc(v_nextExprIdx_106_);
lean_inc(v_newLetDecls_105_);
lean_inc(v_newLocalDeclsForMVars_104_);
lean_inc(v_newLocalDecls_103_);
lean_inc(v_levelArgs_102_);
lean_inc(v_nextLevelIdx_101_);
lean_inc(v_levelParams_100_);
lean_inc(v_visitedExpr_99_);
lean_inc(v_visitedLevel_98_);
lean_dec(v___x_97_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_121_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
lean_inc(v_a_93_);
v___x_113_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_86_, v___x_87_, v_visitedExpr_99_, v_e_78_, v_a_93_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 1, v___x_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_visitedLevel_98_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v_levelParams_100_);
lean_ctor_set(v_reuseFailAlloc_120_, 3, v_nextLevelIdx_101_);
lean_ctor_set(v_reuseFailAlloc_120_, 4, v_levelArgs_102_);
lean_ctor_set(v_reuseFailAlloc_120_, 5, v_newLocalDecls_103_);
lean_ctor_set(v_reuseFailAlloc_120_, 6, v_newLocalDeclsForMVars_104_);
lean_ctor_set(v_reuseFailAlloc_120_, 7, v_newLetDecls_105_);
lean_ctor_set(v_reuseFailAlloc_120_, 8, v_nextExprIdx_106_);
lean_ctor_set(v_reuseFailAlloc_120_, 9, v_exprMVarArgs_107_);
lean_ctor_set(v_reuseFailAlloc_120_, 10, v_exprFVarArgs_108_);
lean_ctor_set(v_reuseFailAlloc_120_, 11, v_toProcess_109_);
v___x_115_ = v_reuseFailAlloc_120_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_116_ = lean_st_ref_put(v_a_80_, v___x_115_);
if (v_isShared_96_ == 0)
{
v___x_118_ = v___x_95_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_93_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_78_);
return v___x_92_;
}
}
else
{
lean_object* v_val_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec_ref(v_e_78_);
lean_dec_ref(v_f_77_);
v_val_123_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_91_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_val_123_);
lean_dec(v___x_91_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set_tag(v___x_125_, 0);
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_val_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_visitExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_77_ = stack[0].m_obj;
lean_object* v_e_78_ = stack[1].m_obj;
lean_object* v_a_79_ = stack[2].m_obj;
lean_object* v_a_80_ = stack[3].m_obj;
lean_object* v_a_81_ = stack[4].m_obj;
lean_object* v_a_82_ = stack[5].m_obj;
lean_object* v_a_83_ = stack[6].m_obj;
lean_object* v_a_84_ = stack[7].m_obj;
lean_object* v_res_135_;
v_res_135_ = l_Lean_Meta_Closure_visitExpr(v_f_77_, v_e_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_visitExpr___boxed(lean_object* v_f_136_, lean_object* v_e_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_Closure_visitExpr(v_f_136_, v_e_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
return v_res_145_;
}
}
lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg(lean_object* v_u_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; lean_object* v_nextLevelIdx_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v_visitedLevel_157_; lean_object* v_visitedExpr_158_; lean_object* v_levelParams_159_; lean_object* v_nextLevelIdx_160_; lean_object* v_levelArgs_161_; lean_object* v_newLocalDecls_162_; lean_object* v_newLocalDeclsForMVars_163_; lean_object* v_newLetDecls_164_; lean_object* v_nextExprIdx_165_; lean_object* v_exprMVarArgs_166_; lean_object* v_exprFVarArgs_167_; lean_object* v_toProcess_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_182_; 
v___x_152_ = lean_st_ref_get(v_a_150_);
v_nextLevelIdx_153_ = lean_ctor_get(v___x_152_, 3);
lean_inc(v_nextLevelIdx_153_);
lean_dec(v___x_152_);
v___x_154_ = ((lean_object*)(l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1));
v___x_155_ = lean_name_append_index_after(v___x_154_, v_nextLevelIdx_153_);
v___x_156_ = lean_st_ref_take(v_a_150_);
v_visitedLevel_157_ = lean_ctor_get(v___x_156_, 0);
v_visitedExpr_158_ = lean_ctor_get(v___x_156_, 1);
v_levelParams_159_ = lean_ctor_get(v___x_156_, 2);
v_nextLevelIdx_160_ = lean_ctor_get(v___x_156_, 3);
v_levelArgs_161_ = lean_ctor_get(v___x_156_, 4);
v_newLocalDecls_162_ = lean_ctor_get(v___x_156_, 5);
v_newLocalDeclsForMVars_163_ = lean_ctor_get(v___x_156_, 6);
v_newLetDecls_164_ = lean_ctor_get(v___x_156_, 7);
v_nextExprIdx_165_ = lean_ctor_get(v___x_156_, 8);
v_exprMVarArgs_166_ = lean_ctor_get(v___x_156_, 9);
v_exprFVarArgs_167_ = lean_ctor_get(v___x_156_, 10);
v_toProcess_168_ = lean_ctor_get(v___x_156_, 11);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_182_ == 0)
{
v___x_170_ = v___x_156_;
v_isShared_171_ = v_isSharedCheck_182_;
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
lean_dec(v___x_156_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_182_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
lean_inc(v___x_155_);
v___x_172_ = lean_array_push(v_levelParams_159_, v___x_155_);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_nextLevelIdx_160_, v___x_173_);
lean_dec(v_nextLevelIdx_160_);
v___x_175_ = lean_array_push(v_levelArgs_161_, v_u_149_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 4, v___x_175_);
lean_ctor_set(v___x_170_, 3, v___x_174_);
lean_ctor_set(v___x_170_, 2, v___x_172_);
v___x_177_ = v___x_170_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_visitedLevel_157_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_visitedExpr_158_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_181_, 4, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_181_, 5, v_newLocalDecls_162_);
lean_ctor_set(v_reuseFailAlloc_181_, 6, v_newLocalDeclsForMVars_163_);
lean_ctor_set(v_reuseFailAlloc_181_, 7, v_newLetDecls_164_);
lean_ctor_set(v_reuseFailAlloc_181_, 8, v_nextExprIdx_165_);
lean_ctor_set(v_reuseFailAlloc_181_, 9, v_exprMVarArgs_166_);
lean_ctor_set(v_reuseFailAlloc_181_, 10, v_exprFVarArgs_167_);
lean_ctor_set(v_reuseFailAlloc_181_, 11, v_toProcess_168_);
v___x_177_ = v_reuseFailAlloc_181_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_st_ref_put(v_a_150_, v___x_177_);
v___x_179_ = l_Lean_mkLevelParam(v___x_155_);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_mkNewLevelParam___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_149_ = stack[0].m_obj;
lean_object* v_a_150_ = stack[1].m_obj;
lean_object* v_res_183_;
v_res_183_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_149_, v_a_150_);
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___redArg___boxed(lean_object* v_u_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_184_, v_a_185_);
lean_dec(v_a_185_);
return v_res_187_;
}
}
lean_object* l_Lean_Meta_Closure_mkNewLevelParam(lean_object* v_u_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_u_188_, v_a_190_);
return v___x_196_;
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_mkNewLevelParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_188_ = stack[0].m_obj;
lean_object* v_a_189_ = stack[1].m_obj;
lean_object* v_a_190_ = stack[2].m_obj;
lean_object* v_a_191_ = stack[3].m_obj;
lean_object* v_a_192_ = stack[4].m_obj;
lean_object* v_a_193_ = stack[5].m_obj;
lean_object* v_a_194_ = stack[6].m_obj;
lean_object* v_res_197_;
v_res_197_ = l_Lean_Meta_Closure_mkNewLevelParam(v_u_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNewLevelParam___boxed(lean_object* v_u_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Meta_Closure_mkNewLevelParam(v_u_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_collectLevelAux_spec__0(lean_object* v_msg_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_box(0);
v___x_209_ = lean_panic_fn_borrowed(v___x_208_, v_msg_207_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(lean_object* v_a_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
lean_object* v___x_212_; 
v___x_212_ = lean_box(0);
return v___x_212_;
}
else
{
lean_object* v_key_213_; lean_object* v_value_214_; lean_object* v_tail_215_; uint8_t v___x_216_; 
v_key_213_ = lean_ctor_get(v_x_211_, 0);
v_value_214_ = lean_ctor_get(v_x_211_, 1);
v_tail_215_ = lean_ctor_get(v_x_211_, 2);
v___x_216_ = lean_level_eq(v_key_213_, v_a_210_);
if (v___x_216_ == 0)
{
v_x_211_ = v_tail_215_;
goto _start;
}
else
{
lean_object* v___x_218_; 
lean_inc(v_value_214_);
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v_value_214_);
return v___x_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg___boxed(lean_object* v_a_219_, lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_219_, v_x_220_);
lean_dec(v_x_220_);
lean_dec(v_a_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(lean_object* v_m_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_buckets_224_; lean_object* v___x_225_; uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v_fold_229_; uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v___x_232_; size_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_buckets_224_ = lean_ctor_get(v_m_222_, 1);
v___x_225_ = lean_array_get_size(v_buckets_224_);
v___x_226_ = l_Lean_Level_hash(v_a_223_);
v___x_227_ = 32ULL;
v___x_228_ = lean_uint64_shift_right(v___x_226_, v___x_227_);
v_fold_229_ = lean_uint64_xor(v___x_226_, v___x_228_);
v___x_230_ = 16ULL;
v___x_231_ = lean_uint64_shift_right(v_fold_229_, v___x_230_);
v___x_232_ = lean_uint64_xor(v_fold_229_, v___x_231_);
v___x_233_ = lean_uint64_to_usize(v___x_232_);
v___x_234_ = lean_usize_of_nat(v___x_225_);
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_sub(v___x_234_, v___x_235_);
v___x_237_ = lean_usize_land(v___x_233_, v___x_236_);
v___x_238_ = lean_array_uget_borrowed(v_buckets_224_, v___x_237_);
v___x_239_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_223_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg___boxed(lean_object* v_m_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_240_, v_a_241_);
lean_dec(v_a_241_);
lean_dec_ref(v_m_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
return v_x_243_;
}
else
{
lean_object* v_key_245_; lean_object* v_value_246_; lean_object* v_tail_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_270_; 
v_key_245_ = lean_ctor_get(v_x_244_, 0);
v_value_246_ = lean_ctor_get(v_x_244_, 1);
v_tail_247_ = lean_ctor_get(v_x_244_, 2);
v_isSharedCheck_270_ = !lean_is_exclusive(v_x_244_);
if (v_isSharedCheck_270_ == 0)
{
v___x_249_ = v_x_244_;
v_isShared_250_ = v_isSharedCheck_270_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_tail_247_);
lean_inc(v_value_246_);
lean_inc(v_key_245_);
lean_dec(v_x_244_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_270_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; uint64_t v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v_fold_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; size_t v___x_259_; size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_251_ = lean_array_get_size(v_x_243_);
v___x_252_ = l_Lean_Level_hash(v_key_245_);
v___x_253_ = 32ULL;
v___x_254_ = lean_uint64_shift_right(v___x_252_, v___x_253_);
v_fold_255_ = lean_uint64_xor(v___x_252_, v___x_254_);
v___x_256_ = 16ULL;
v___x_257_ = lean_uint64_shift_right(v_fold_255_, v___x_256_);
v___x_258_ = lean_uint64_xor(v_fold_255_, v___x_257_);
v___x_259_ = lean_uint64_to_usize(v___x_258_);
v___x_260_ = lean_usize_of_nat(v___x_251_);
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_sub(v___x_260_, v___x_261_);
v___x_263_ = lean_usize_land(v___x_259_, v___x_262_);
v___x_264_ = lean_array_uget_borrowed(v_x_243_, v___x_263_);
lean_inc(v___x_264_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 2, v___x_264_);
v___x_266_ = v___x_249_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_key_245_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_value_246_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v___x_264_);
v___x_266_ = v_reuseFailAlloc_269_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; 
v___x_267_ = lean_array_uset(v_x_243_, v___x_263_, v___x_266_);
v_x_243_ = v___x_267_;
v_x_244_ = v_tail_247_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(lean_object* v_i_271_, lean_object* v_source_272_, lean_object* v_target_273_){
_start:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_array_get_size(v_source_272_);
v___x_275_ = lean_nat_dec_lt(v_i_271_, v___x_274_);
if (v___x_275_ == 0)
{
lean_dec_ref(v_source_272_);
lean_dec(v_i_271_);
return v_target_273_;
}
else
{
lean_object* v_es_276_; lean_object* v___x_277_; lean_object* v_source_278_; lean_object* v_target_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_es_276_ = lean_array_fget(v_source_272_, v_i_271_);
v___x_277_ = lean_box(0);
v_source_278_ = lean_array_fset(v_source_272_, v_i_271_, v___x_277_);
v_target_279_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_target_273_, v_es_276_);
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_add(v_i_271_, v___x_280_);
lean_dec(v_i_271_);
v_i_271_ = v___x_281_;
v_source_272_ = v_source_278_;
v_target_273_ = v_target_279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(lean_object* v_data_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_nbuckets_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_284_ = lean_array_get_size(v_data_283_);
v___x_285_ = lean_unsigned_to_nat(2u);
v_nbuckets_286_ = lean_nat_mul(v___x_284_, v___x_285_);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_box(0);
v___x_289_ = lean_mk_array(v_nbuckets_286_, v___x_288_);
v___x_290_ = lean_array_propagate_mark(v_data_283_, v___x_289_);
v___x_291_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v___x_287_, v_data_283_, v___x_290_);
return v___x_291_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(lean_object* v_a_292_, lean_object* v_x_293_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_292_ = stack[0].m_obj;
lean_object* v_x_293_ = stack[1].m_obj;
uint8_t v_res_299_;
v_res_299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_292_, v_x_293_);
stack->m_num = v_res_299_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg___boxed(lean_object* v_a_300_, lean_object* v_x_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_300_, v_x_301_);
lean_dec(v_x_301_);
lean_dec(v_a_300_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(lean_object* v_a_304_, lean_object* v_b_305_, lean_object* v_x_306_){
_start:
{
if (lean_obj_tag(v_x_306_) == 0)
{
lean_dec(v_b_305_);
lean_dec(v_a_304_);
return v_x_306_;
}
else
{
lean_object* v_key_307_; lean_object* v_value_308_; lean_object* v_tail_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_321_; 
v_key_307_ = lean_ctor_get(v_x_306_, 0);
v_value_308_ = lean_ctor_get(v_x_306_, 1);
v_tail_309_ = lean_ctor_get(v_x_306_, 2);
v_isSharedCheck_321_ = !lean_is_exclusive(v_x_306_);
if (v_isSharedCheck_321_ == 0)
{
v___x_311_ = v_x_306_;
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_tail_309_);
lean_inc(v_value_308_);
lean_inc(v_key_307_);
lean_dec(v_x_306_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
uint8_t v___x_313_; 
v___x_313_ = lean_level_eq(v_key_307_, v_a_304_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_314_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_304_, v_b_305_, v_tail_309_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 2, v___x_314_);
v___x_316_ = v___x_311_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_key_307_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_value_308_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
else
{
lean_object* v___x_319_; 
lean_dec(v_value_308_);
lean_dec(v_key_307_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v_b_305_);
lean_ctor_set(v___x_311_, 0, v_a_304_);
v___x_319_ = v___x_311_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_304_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_b_305_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_tail_309_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(lean_object* v_m_322_, lean_object* v_a_323_, lean_object* v_b_324_){
_start:
{
lean_object* v_size_325_; lean_object* v_buckets_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_369_; 
v_size_325_ = lean_ctor_get(v_m_322_, 0);
v_buckets_326_ = lean_ctor_get(v_m_322_, 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v_m_322_);
if (v_isSharedCheck_369_ == 0)
{
v___x_328_ = v_m_322_;
v_isShared_329_ = v_isSharedCheck_369_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_buckets_326_);
lean_inc(v_size_325_);
lean_dec(v_m_322_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_369_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v_fold_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; lean_object* v_bkt_343_; uint8_t v___x_344_; 
v___x_330_ = lean_array_get_size(v_buckets_326_);
v___x_331_ = l_Lean_Level_hash(v_a_323_);
v___x_332_ = 32ULL;
v___x_333_ = lean_uint64_shift_right(v___x_331_, v___x_332_);
v_fold_334_ = lean_uint64_xor(v___x_331_, v___x_333_);
v___x_335_ = 16ULL;
v___x_336_ = lean_uint64_shift_right(v_fold_334_, v___x_335_);
v___x_337_ = lean_uint64_xor(v_fold_334_, v___x_336_);
v___x_338_ = lean_uint64_to_usize(v___x_337_);
v___x_339_ = lean_usize_of_nat(v___x_330_);
v___x_340_ = ((size_t)1ULL);
v___x_341_ = lean_usize_sub(v___x_339_, v___x_340_);
v___x_342_ = lean_usize_land(v___x_338_, v___x_341_);
v_bkt_343_ = lean_array_uget_borrowed(v_buckets_326_, v___x_342_);
v___x_344_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_323_, v_bkt_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v_size_x27_346_; lean_object* v___x_347_; lean_object* v_buckets_x27_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_345_ = lean_unsigned_to_nat(1u);
v_size_x27_346_ = lean_nat_add(v_size_325_, v___x_345_);
lean_dec(v_size_325_);
lean_inc(v_bkt_343_);
v___x_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_347_, 0, v_a_323_);
lean_ctor_set(v___x_347_, 1, v_b_324_);
lean_ctor_set(v___x_347_, 2, v_bkt_343_);
v_buckets_x27_348_ = lean_array_uset(v_buckets_326_, v___x_342_, v___x_347_);
v___x_349_ = lean_unsigned_to_nat(4u);
v___x_350_ = lean_nat_mul(v_size_x27_346_, v___x_349_);
v___x_351_ = lean_unsigned_to_nat(3u);
v___x_352_ = lean_nat_div(v___x_350_, v___x_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_array_get_size(v_buckets_x27_348_);
v___x_354_ = lean_nat_dec_le(v___x_352_, v___x_353_);
lean_dec(v___x_352_);
if (v___x_354_ == 0)
{
lean_object* v_val_355_; lean_object* v___x_357_; 
v_val_355_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_buckets_x27_348_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v_val_355_);
lean_ctor_set(v___x_328_, 0, v_size_x27_346_);
v___x_357_ = v___x_328_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_size_x27_346_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_val_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
else
{
lean_object* v___x_360_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v_buckets_x27_348_);
lean_ctor_set(v___x_328_, 0, v_size_x27_346_);
v___x_360_ = v___x_328_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_size_x27_346_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_buckets_x27_348_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
else
{
lean_object* v___x_362_; lean_object* v_buckets_x27_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
lean_inc(v_bkt_343_);
v___x_362_ = lean_box(0);
v_buckets_x27_363_ = lean_array_uset(v_buckets_326_, v___x_342_, v___x_362_);
v___x_364_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_323_, v_b_324_, v_bkt_343_);
v___x_365_ = lean_array_uset(v_buckets_x27_363_, v___x_342_, v___x_364_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_365_);
v___x_367_ = v___x_328_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_size_325_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg(lean_object* v_x_370_, lean_object* v_a_371_){
_start:
{
switch(lean_obj_tag(v_x_370_))
{
case 0:
{
lean_object* v___x_373_; 
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v_x_370_);
return v___x_373_;
}
case 1:
{
lean_object* v_a_374_; lean_object* v_a_376_; uint8_t v___x_413_; 
v_a_374_ = lean_ctor_get(v_x_370_, 0);
v___x_413_ = l_Lean_Level_hasMVar(v_a_374_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; 
v___x_414_ = l_Lean_Level_hasParam(v_a_374_);
if (v___x_414_ == 0)
{
lean_inc(v_a_374_);
v_a_376_ = v_a_374_;
goto v___jp_375_;
}
else
{
goto v___jp_383_;
}
}
else
{
goto v___jp_383_;
}
v___jp_375_:
{
size_t v___x_377_; size_t v___x_378_; uint8_t v___x_379_; 
v___x_377_ = lean_ptr_addr(v_a_374_);
v___x_378_ = lean_ptr_addr(v_a_376_);
v___x_379_ = lean_usize_dec_eq(v___x_377_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec_ref_known(v_x_370_, 1);
v___x_380_ = l_Lean_Level_succ___override(v_a_376_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; 
lean_dec(v_a_376_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v_x_370_);
return v___x_382_;
}
}
v___jp_383_:
{
lean_object* v___x_384_; lean_object* v_visitedLevel_385_; lean_object* v___x_386_; 
v___x_384_ = lean_st_ref_get(v_a_371_);
v_visitedLevel_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc_ref(v_visitedLevel_385_);
lean_dec(v___x_384_);
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_385_, v_a_374_);
lean_dec_ref(v_visitedLevel_385_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v___x_387_; 
lean_inc(v_a_374_);
v___x_387_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_374_, v_a_371_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; lean_object* v_visitedLevel_390_; lean_object* v_visitedExpr_391_; lean_object* v_levelParams_392_; lean_object* v_nextLevelIdx_393_; lean_object* v_levelArgs_394_; lean_object* v_newLocalDecls_395_; lean_object* v_newLocalDeclsForMVars_396_; lean_object* v_newLetDecls_397_; lean_object* v_nextExprIdx_398_; lean_object* v_exprMVarArgs_399_; lean_object* v_exprFVarArgs_400_; lean_object* v_toProcess_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_410_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 1);
v___x_389_ = lean_st_ref_take(v_a_371_);
v_visitedLevel_390_ = lean_ctor_get(v___x_389_, 0);
v_visitedExpr_391_ = lean_ctor_get(v___x_389_, 1);
v_levelParams_392_ = lean_ctor_get(v___x_389_, 2);
v_nextLevelIdx_393_ = lean_ctor_get(v___x_389_, 3);
v_levelArgs_394_ = lean_ctor_get(v___x_389_, 4);
v_newLocalDecls_395_ = lean_ctor_get(v___x_389_, 5);
v_newLocalDeclsForMVars_396_ = lean_ctor_get(v___x_389_, 6);
v_newLetDecls_397_ = lean_ctor_get(v___x_389_, 7);
v_nextExprIdx_398_ = lean_ctor_get(v___x_389_, 8);
v_exprMVarArgs_399_ = lean_ctor_get(v___x_389_, 9);
v_exprFVarArgs_400_ = lean_ctor_get(v___x_389_, 10);
v_toProcess_401_ = lean_ctor_get(v___x_389_, 11);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_410_ == 0)
{
v___x_403_ = v___x_389_;
v_isShared_404_ = v_isSharedCheck_410_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_toProcess_401_);
lean_inc(v_exprFVarArgs_400_);
lean_inc(v_exprMVarArgs_399_);
lean_inc(v_nextExprIdx_398_);
lean_inc(v_newLetDecls_397_);
lean_inc(v_newLocalDeclsForMVars_396_);
lean_inc(v_newLocalDecls_395_);
lean_inc(v_levelArgs_394_);
lean_inc(v_nextLevelIdx_393_);
lean_inc(v_levelParams_392_);
lean_inc(v_visitedExpr_391_);
lean_inc(v_visitedLevel_390_);
lean_dec(v___x_389_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_410_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
lean_inc(v_a_388_);
lean_inc(v_a_374_);
v___x_405_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_390_, v_a_374_, v_a_388_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_visitedExpr_391_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_levelParams_392_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_nextLevelIdx_393_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_levelArgs_394_);
lean_ctor_set(v_reuseFailAlloc_409_, 5, v_newLocalDecls_395_);
lean_ctor_set(v_reuseFailAlloc_409_, 6, v_newLocalDeclsForMVars_396_);
lean_ctor_set(v_reuseFailAlloc_409_, 7, v_newLetDecls_397_);
lean_ctor_set(v_reuseFailAlloc_409_, 8, v_nextExprIdx_398_);
lean_ctor_set(v_reuseFailAlloc_409_, 9, v_exprMVarArgs_399_);
lean_ctor_set(v_reuseFailAlloc_409_, 10, v_exprFVarArgs_400_);
lean_ctor_set(v_reuseFailAlloc_409_, 11, v_toProcess_401_);
v___x_407_ = v_reuseFailAlloc_409_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; 
v___x_408_ = lean_st_ref_put(v_a_371_, v___x_407_);
v_a_376_ = v_a_388_;
goto v___jp_375_;
}
}
}
else
{
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_411_; 
v_a_411_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_387_, 1);
v_a_376_ = v_a_411_;
goto v___jp_375_;
}
else
{
lean_dec_ref_known(v_x_370_, 1);
return v___x_387_;
}
}
}
else
{
lean_object* v_val_412_; 
v_val_412_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_val_412_);
lean_dec_ref_known(v___x_386_, 1);
v_a_376_ = v_val_412_;
goto v___jp_375_;
}
}
}
case 2:
{
lean_object* v_a_415_; lean_object* v_a_416_; lean_object* v___y_418_; lean_object* v_a_419_; lean_object* v___y_433_; lean_object* v_a_464_; uint8_t v___x_497_; 
v_a_415_ = lean_ctor_get(v_x_370_, 0);
v_a_416_ = lean_ctor_get(v_x_370_, 1);
v___x_497_ = l_Lean_Level_hasMVar(v_a_415_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; 
v___x_498_ = l_Lean_Level_hasParam(v_a_415_);
if (v___x_498_ == 0)
{
lean_inc(v_a_415_);
v_a_464_ = v_a_415_;
goto v___jp_463_;
}
else
{
goto v___jp_467_;
}
}
else
{
goto v___jp_467_;
}
v___jp_417_:
{
size_t v___x_420_; size_t v___x_421_; uint8_t v___x_422_; 
v___x_420_ = lean_ptr_addr(v_a_415_);
v___x_421_ = lean_ptr_addr(v___y_418_);
v___x_422_ = lean_usize_dec_eq(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref_known(v_x_370_, 2);
v___x_423_ = l_Lean_mkLevelMax_x27(v___y_418_, v_a_419_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
else
{
size_t v___x_425_; size_t v___x_426_; uint8_t v___x_427_; 
v___x_425_ = lean_ptr_addr(v_a_416_);
v___x_426_ = lean_ptr_addr(v_a_419_);
v___x_427_ = lean_usize_dec_eq(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec_ref_known(v_x_370_, 2);
v___x_428_ = l_Lean_mkLevelMax_x27(v___y_418_, v_a_419_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = l_Lean_simpLevelMax_x27(v___y_418_, v_a_419_, v_x_370_);
lean_dec_ref_known(v_x_370_, 2);
lean_dec(v_a_419_);
lean_dec(v___y_418_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
}
v___jp_432_:
{
lean_object* v___x_434_; lean_object* v_visitedLevel_435_; lean_object* v___x_436_; 
v___x_434_ = lean_st_ref_get(v_a_371_);
v_visitedLevel_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc_ref(v_visitedLevel_435_);
lean_dec(v___x_434_);
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_435_, v_a_416_);
lean_dec_ref(v_visitedLevel_435_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v___x_437_; 
lean_inc(v_a_416_);
v___x_437_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_416_, v_a_371_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; lean_object* v_visitedLevel_440_; lean_object* v_visitedExpr_441_; lean_object* v_levelParams_442_; lean_object* v_nextLevelIdx_443_; lean_object* v_levelArgs_444_; lean_object* v_newLocalDecls_445_; lean_object* v_newLocalDeclsForMVars_446_; lean_object* v_newLetDecls_447_; lean_object* v_nextExprIdx_448_; lean_object* v_exprMVarArgs_449_; lean_object* v_exprFVarArgs_450_; lean_object* v_toProcess_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_460_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = lean_st_ref_take(v_a_371_);
v_visitedLevel_440_ = lean_ctor_get(v___x_439_, 0);
v_visitedExpr_441_ = lean_ctor_get(v___x_439_, 1);
v_levelParams_442_ = lean_ctor_get(v___x_439_, 2);
v_nextLevelIdx_443_ = lean_ctor_get(v___x_439_, 3);
v_levelArgs_444_ = lean_ctor_get(v___x_439_, 4);
v_newLocalDecls_445_ = lean_ctor_get(v___x_439_, 5);
v_newLocalDeclsForMVars_446_ = lean_ctor_get(v___x_439_, 6);
v_newLetDecls_447_ = lean_ctor_get(v___x_439_, 7);
v_nextExprIdx_448_ = lean_ctor_get(v___x_439_, 8);
v_exprMVarArgs_449_ = lean_ctor_get(v___x_439_, 9);
v_exprFVarArgs_450_ = lean_ctor_get(v___x_439_, 10);
v_toProcess_451_ = lean_ctor_get(v___x_439_, 11);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_460_ == 0)
{
v___x_453_ = v___x_439_;
v_isShared_454_ = v_isSharedCheck_460_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_toProcess_451_);
lean_inc(v_exprFVarArgs_450_);
lean_inc(v_exprMVarArgs_449_);
lean_inc(v_nextExprIdx_448_);
lean_inc(v_newLetDecls_447_);
lean_inc(v_newLocalDeclsForMVars_446_);
lean_inc(v_newLocalDecls_445_);
lean_inc(v_levelArgs_444_);
lean_inc(v_nextLevelIdx_443_);
lean_inc(v_levelParams_442_);
lean_inc(v_visitedExpr_441_);
lean_inc(v_visitedLevel_440_);
lean_dec(v___x_439_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_460_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
lean_inc(v_a_438_);
lean_inc(v_a_416_);
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_440_, v_a_416_, v_a_438_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_455_);
v___x_457_ = v___x_453_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_visitedExpr_441_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_levelParams_442_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_nextLevelIdx_443_);
lean_ctor_set(v_reuseFailAlloc_459_, 4, v_levelArgs_444_);
lean_ctor_set(v_reuseFailAlloc_459_, 5, v_newLocalDecls_445_);
lean_ctor_set(v_reuseFailAlloc_459_, 6, v_newLocalDeclsForMVars_446_);
lean_ctor_set(v_reuseFailAlloc_459_, 7, v_newLetDecls_447_);
lean_ctor_set(v_reuseFailAlloc_459_, 8, v_nextExprIdx_448_);
lean_ctor_set(v_reuseFailAlloc_459_, 9, v_exprMVarArgs_449_);
lean_ctor_set(v_reuseFailAlloc_459_, 10, v_exprFVarArgs_450_);
lean_ctor_set(v_reuseFailAlloc_459_, 11, v_toProcess_451_);
v___x_457_ = v_reuseFailAlloc_459_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; 
v___x_458_ = lean_st_ref_put(v_a_371_, v___x_457_);
v___y_418_ = v___y_433_;
v_a_419_ = v_a_438_;
goto v___jp_417_;
}
}
}
else
{
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_461_; 
v_a_461_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_437_, 1);
v___y_418_ = v___y_433_;
v_a_419_ = v_a_461_;
goto v___jp_417_;
}
else
{
lean_dec(v___y_433_);
lean_dec_ref_known(v_x_370_, 2);
return v___x_437_;
}
}
}
else
{
lean_object* v_val_462_; 
v_val_462_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_462_);
lean_dec_ref_known(v___x_436_, 1);
v___y_418_ = v___y_433_;
v_a_419_ = v_val_462_;
goto v___jp_417_;
}
}
v___jp_463_:
{
uint8_t v___x_465_; 
v___x_465_ = l_Lean_Level_hasMVar(v_a_416_);
if (v___x_465_ == 0)
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_Level_hasParam(v_a_416_);
if (v___x_466_ == 0)
{
lean_inc(v_a_416_);
v___y_418_ = v_a_464_;
v_a_419_ = v_a_416_;
goto v___jp_417_;
}
else
{
v___y_433_ = v_a_464_;
goto v___jp_432_;
}
}
else
{
v___y_433_ = v_a_464_;
goto v___jp_432_;
}
}
v___jp_467_:
{
lean_object* v___x_468_; lean_object* v_visitedLevel_469_; lean_object* v___x_470_; 
v___x_468_ = lean_st_ref_get(v_a_371_);
v_visitedLevel_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc_ref(v_visitedLevel_469_);
lean_dec(v___x_468_);
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_469_, v_a_415_);
lean_dec_ref(v_visitedLevel_469_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v___x_471_; 
lean_inc(v_a_415_);
v___x_471_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_415_, v_a_371_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; lean_object* v_visitedLevel_474_; lean_object* v_visitedExpr_475_; lean_object* v_levelParams_476_; lean_object* v_nextLevelIdx_477_; lean_object* v_levelArgs_478_; lean_object* v_newLocalDecls_479_; lean_object* v_newLocalDeclsForMVars_480_; lean_object* v_newLetDecls_481_; lean_object* v_nextExprIdx_482_; lean_object* v_exprMVarArgs_483_; lean_object* v_exprFVarArgs_484_; lean_object* v_toProcess_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_494_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
v___x_473_ = lean_st_ref_take(v_a_371_);
v_visitedLevel_474_ = lean_ctor_get(v___x_473_, 0);
v_visitedExpr_475_ = lean_ctor_get(v___x_473_, 1);
v_levelParams_476_ = lean_ctor_get(v___x_473_, 2);
v_nextLevelIdx_477_ = lean_ctor_get(v___x_473_, 3);
v_levelArgs_478_ = lean_ctor_get(v___x_473_, 4);
v_newLocalDecls_479_ = lean_ctor_get(v___x_473_, 5);
v_newLocalDeclsForMVars_480_ = lean_ctor_get(v___x_473_, 6);
v_newLetDecls_481_ = lean_ctor_get(v___x_473_, 7);
v_nextExprIdx_482_ = lean_ctor_get(v___x_473_, 8);
v_exprMVarArgs_483_ = lean_ctor_get(v___x_473_, 9);
v_exprFVarArgs_484_ = lean_ctor_get(v___x_473_, 10);
v_toProcess_485_ = lean_ctor_get(v___x_473_, 11);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_494_ == 0)
{
v___x_487_ = v___x_473_;
v_isShared_488_ = v_isSharedCheck_494_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_toProcess_485_);
lean_inc(v_exprFVarArgs_484_);
lean_inc(v_exprMVarArgs_483_);
lean_inc(v_nextExprIdx_482_);
lean_inc(v_newLetDecls_481_);
lean_inc(v_newLocalDeclsForMVars_480_);
lean_inc(v_newLocalDecls_479_);
lean_inc(v_levelArgs_478_);
lean_inc(v_nextLevelIdx_477_);
lean_inc(v_levelParams_476_);
lean_inc(v_visitedExpr_475_);
lean_inc(v_visitedLevel_474_);
lean_dec(v___x_473_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_494_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
lean_inc(v_a_472_);
lean_inc(v_a_415_);
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_474_, v_a_415_, v_a_472_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_visitedExpr_475_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_levelParams_476_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_nextLevelIdx_477_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v_levelArgs_478_);
lean_ctor_set(v_reuseFailAlloc_493_, 5, v_newLocalDecls_479_);
lean_ctor_set(v_reuseFailAlloc_493_, 6, v_newLocalDeclsForMVars_480_);
lean_ctor_set(v_reuseFailAlloc_493_, 7, v_newLetDecls_481_);
lean_ctor_set(v_reuseFailAlloc_493_, 8, v_nextExprIdx_482_);
lean_ctor_set(v_reuseFailAlloc_493_, 9, v_exprMVarArgs_483_);
lean_ctor_set(v_reuseFailAlloc_493_, 10, v_exprFVarArgs_484_);
lean_ctor_set(v_reuseFailAlloc_493_, 11, v_toProcess_485_);
v___x_491_ = v_reuseFailAlloc_493_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; 
v___x_492_ = lean_st_ref_put(v_a_371_, v___x_491_);
v_a_464_ = v_a_472_;
goto v___jp_463_;
}
}
}
else
{
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_495_; 
v_a_495_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_495_);
lean_dec_ref_known(v___x_471_, 1);
v_a_464_ = v_a_495_;
goto v___jp_463_;
}
else
{
lean_dec_ref_known(v_x_370_, 2);
return v___x_471_;
}
}
}
else
{
lean_object* v_val_496_; 
v_val_496_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_val_496_);
lean_dec_ref_known(v___x_470_, 1);
v_a_464_ = v_val_496_;
goto v___jp_463_;
}
}
}
case 3:
{
lean_object* v_a_499_; lean_object* v_a_500_; lean_object* v___y_502_; lean_object* v_a_503_; lean_object* v___y_517_; lean_object* v_a_548_; uint8_t v___x_581_; 
v_a_499_ = lean_ctor_get(v_x_370_, 0);
v_a_500_ = lean_ctor_get(v_x_370_, 1);
v___x_581_ = l_Lean_Level_hasMVar(v_a_499_);
if (v___x_581_ == 0)
{
uint8_t v___x_582_; 
v___x_582_ = l_Lean_Level_hasParam(v_a_499_);
if (v___x_582_ == 0)
{
lean_inc(v_a_499_);
v_a_548_ = v_a_499_;
goto v___jp_547_;
}
else
{
goto v___jp_551_;
}
}
else
{
goto v___jp_551_;
}
v___jp_501_:
{
size_t v___x_504_; size_t v___x_505_; uint8_t v___x_506_; 
v___x_504_ = lean_ptr_addr(v_a_499_);
v___x_505_ = lean_ptr_addr(v___y_502_);
v___x_506_ = lean_usize_dec_eq(v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec_ref_known(v_x_370_, 2);
v___x_507_ = l_Lean_mkLevelIMax_x27(v___y_502_, v_a_503_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
else
{
size_t v___x_509_; size_t v___x_510_; uint8_t v___x_511_; 
v___x_509_ = lean_ptr_addr(v_a_500_);
v___x_510_ = lean_ptr_addr(v_a_503_);
v___x_511_ = lean_usize_dec_eq(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec_ref_known(v_x_370_, 2);
v___x_512_ = l_Lean_mkLevelIMax_x27(v___y_502_, v_a_503_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = l_Lean_simpLevelIMax_x27(v___y_502_, v_a_503_, v_x_370_);
lean_dec_ref_known(v_x_370_, 2);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v_visitedLevel_519_; lean_object* v___x_520_; 
v___x_518_ = lean_st_ref_get(v_a_371_);
v_visitedLevel_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc_ref(v_visitedLevel_519_);
lean_dec(v___x_518_);
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_519_, v_a_500_);
lean_dec_ref(v_visitedLevel_519_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v___x_521_; 
lean_inc(v_a_500_);
v___x_521_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_500_, v_a_371_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; lean_object* v_visitedLevel_524_; lean_object* v_visitedExpr_525_; lean_object* v_levelParams_526_; lean_object* v_nextLevelIdx_527_; lean_object* v_levelArgs_528_; lean_object* v_newLocalDecls_529_; lean_object* v_newLocalDeclsForMVars_530_; lean_object* v_newLetDecls_531_; lean_object* v_nextExprIdx_532_; lean_object* v_exprMVarArgs_533_; lean_object* v_exprFVarArgs_534_; lean_object* v_toProcess_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_544_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = lean_st_ref_take(v_a_371_);
v_visitedLevel_524_ = lean_ctor_get(v___x_523_, 0);
v_visitedExpr_525_ = lean_ctor_get(v___x_523_, 1);
v_levelParams_526_ = lean_ctor_get(v___x_523_, 2);
v_nextLevelIdx_527_ = lean_ctor_get(v___x_523_, 3);
v_levelArgs_528_ = lean_ctor_get(v___x_523_, 4);
v_newLocalDecls_529_ = lean_ctor_get(v___x_523_, 5);
v_newLocalDeclsForMVars_530_ = lean_ctor_get(v___x_523_, 6);
v_newLetDecls_531_ = lean_ctor_get(v___x_523_, 7);
v_nextExprIdx_532_ = lean_ctor_get(v___x_523_, 8);
v_exprMVarArgs_533_ = lean_ctor_get(v___x_523_, 9);
v_exprFVarArgs_534_ = lean_ctor_get(v___x_523_, 10);
v_toProcess_535_ = lean_ctor_get(v___x_523_, 11);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_544_ == 0)
{
v___x_537_ = v___x_523_;
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_toProcess_535_);
lean_inc(v_exprFVarArgs_534_);
lean_inc(v_exprMVarArgs_533_);
lean_inc(v_nextExprIdx_532_);
lean_inc(v_newLetDecls_531_);
lean_inc(v_newLocalDeclsForMVars_530_);
lean_inc(v_newLocalDecls_529_);
lean_inc(v_levelArgs_528_);
lean_inc(v_nextLevelIdx_527_);
lean_inc(v_levelParams_526_);
lean_inc(v_visitedExpr_525_);
lean_inc(v_visitedLevel_524_);
lean_dec(v___x_523_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
lean_inc(v_a_522_);
lean_inc(v_a_500_);
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_524_, v_a_500_, v_a_522_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_539_);
v___x_541_ = v___x_537_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_visitedExpr_525_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_levelParams_526_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v_nextLevelIdx_527_);
lean_ctor_set(v_reuseFailAlloc_543_, 4, v_levelArgs_528_);
lean_ctor_set(v_reuseFailAlloc_543_, 5, v_newLocalDecls_529_);
lean_ctor_set(v_reuseFailAlloc_543_, 6, v_newLocalDeclsForMVars_530_);
lean_ctor_set(v_reuseFailAlloc_543_, 7, v_newLetDecls_531_);
lean_ctor_set(v_reuseFailAlloc_543_, 8, v_nextExprIdx_532_);
lean_ctor_set(v_reuseFailAlloc_543_, 9, v_exprMVarArgs_533_);
lean_ctor_set(v_reuseFailAlloc_543_, 10, v_exprFVarArgs_534_);
lean_ctor_set(v_reuseFailAlloc_543_, 11, v_toProcess_535_);
v___x_541_ = v_reuseFailAlloc_543_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; 
v___x_542_ = lean_st_ref_put(v_a_371_, v___x_541_);
v___y_502_ = v___y_517_;
v_a_503_ = v_a_522_;
goto v___jp_501_;
}
}
}
else
{
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_521_, 1);
v___y_502_ = v___y_517_;
v_a_503_ = v_a_545_;
goto v___jp_501_;
}
else
{
lean_dec(v___y_517_);
lean_dec_ref_known(v_x_370_, 2);
return v___x_521_;
}
}
}
else
{
lean_object* v_val_546_; 
v_val_546_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_520_, 1);
v___y_502_ = v___y_517_;
v_a_503_ = v_val_546_;
goto v___jp_501_;
}
}
v___jp_547_:
{
uint8_t v___x_549_; 
v___x_549_ = l_Lean_Level_hasMVar(v_a_500_);
if (v___x_549_ == 0)
{
uint8_t v___x_550_; 
v___x_550_ = l_Lean_Level_hasParam(v_a_500_);
if (v___x_550_ == 0)
{
lean_inc(v_a_500_);
v___y_502_ = v_a_548_;
v_a_503_ = v_a_500_;
goto v___jp_501_;
}
else
{
v___y_517_ = v_a_548_;
goto v___jp_516_;
}
}
else
{
v___y_517_ = v_a_548_;
goto v___jp_516_;
}
}
v___jp_551_:
{
lean_object* v___x_552_; lean_object* v_visitedLevel_553_; lean_object* v___x_554_; 
v___x_552_ = lean_st_ref_get(v_a_371_);
v_visitedLevel_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc_ref(v_visitedLevel_553_);
lean_dec(v___x_552_);
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_553_, v_a_499_);
lean_dec_ref(v_visitedLevel_553_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_555_; 
lean_inc(v_a_499_);
v___x_555_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_a_499_, v_a_371_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_557_; lean_object* v_visitedLevel_558_; lean_object* v_visitedExpr_559_; lean_object* v_levelParams_560_; lean_object* v_nextLevelIdx_561_; lean_object* v_levelArgs_562_; lean_object* v_newLocalDecls_563_; lean_object* v_newLocalDeclsForMVars_564_; lean_object* v_newLetDecls_565_; lean_object* v_nextExprIdx_566_; lean_object* v_exprMVarArgs_567_; lean_object* v_exprFVarArgs_568_; lean_object* v_toProcess_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_578_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v___x_555_, 1);
v___x_557_ = lean_st_ref_take(v_a_371_);
v_visitedLevel_558_ = lean_ctor_get(v___x_557_, 0);
v_visitedExpr_559_ = lean_ctor_get(v___x_557_, 1);
v_levelParams_560_ = lean_ctor_get(v___x_557_, 2);
v_nextLevelIdx_561_ = lean_ctor_get(v___x_557_, 3);
v_levelArgs_562_ = lean_ctor_get(v___x_557_, 4);
v_newLocalDecls_563_ = lean_ctor_get(v___x_557_, 5);
v_newLocalDeclsForMVars_564_ = lean_ctor_get(v___x_557_, 6);
v_newLetDecls_565_ = lean_ctor_get(v___x_557_, 7);
v_nextExprIdx_566_ = lean_ctor_get(v___x_557_, 8);
v_exprMVarArgs_567_ = lean_ctor_get(v___x_557_, 9);
v_exprFVarArgs_568_ = lean_ctor_get(v___x_557_, 10);
v_toProcess_569_ = lean_ctor_get(v___x_557_, 11);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_578_ == 0)
{
v___x_571_ = v___x_557_;
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_toProcess_569_);
lean_inc(v_exprFVarArgs_568_);
lean_inc(v_exprMVarArgs_567_);
lean_inc(v_nextExprIdx_566_);
lean_inc(v_newLetDecls_565_);
lean_inc(v_newLocalDeclsForMVars_564_);
lean_inc(v_newLocalDecls_563_);
lean_inc(v_levelArgs_562_);
lean_inc(v_nextLevelIdx_561_);
lean_inc(v_levelParams_560_);
lean_inc(v_visitedExpr_559_);
lean_inc(v_visitedLevel_558_);
lean_dec(v___x_557_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_575_; 
lean_inc(v_a_556_);
lean_inc(v_a_499_);
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_558_, v_a_499_, v_a_556_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_573_);
v___x_575_ = v___x_571_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_visitedExpr_559_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_levelParams_560_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v_nextLevelIdx_561_);
lean_ctor_set(v_reuseFailAlloc_577_, 4, v_levelArgs_562_);
lean_ctor_set(v_reuseFailAlloc_577_, 5, v_newLocalDecls_563_);
lean_ctor_set(v_reuseFailAlloc_577_, 6, v_newLocalDeclsForMVars_564_);
lean_ctor_set(v_reuseFailAlloc_577_, 7, v_newLetDecls_565_);
lean_ctor_set(v_reuseFailAlloc_577_, 8, v_nextExprIdx_566_);
lean_ctor_set(v_reuseFailAlloc_577_, 9, v_exprMVarArgs_567_);
lean_ctor_set(v_reuseFailAlloc_577_, 10, v_exprFVarArgs_568_);
lean_ctor_set(v_reuseFailAlloc_577_, 11, v_toProcess_569_);
v___x_575_ = v_reuseFailAlloc_577_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_st_ref_put(v_a_371_, v___x_575_);
v_a_548_ = v_a_556_;
goto v___jp_547_;
}
}
}
else
{
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_579_; 
v_a_579_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_555_, 1);
v_a_548_ = v_a_579_;
goto v___jp_547_;
}
else
{
lean_dec_ref_known(v_x_370_, 2);
return v___x_555_;
}
}
}
else
{
lean_object* v_val_580_; 
v_val_580_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_val_580_);
lean_dec_ref_known(v___x_554_, 1);
v_a_548_ = v_val_580_;
goto v___jp_547_;
}
}
}
default: 
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Meta_Closure_mkNewLevelParam___redArg(v_x_370_, v_a_371_);
return v___x_583_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_collectLevelAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_370_ = stack[0].m_obj;
lean_object* v_a_371_ = stack[1].m_obj;
lean_object* v_res_584_;
v_res_584_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_370_, v_a_371_);
stack->m_obj
 = v_res_584_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object* v_x_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_585_, v_a_586_);
lean_dec(v_a_586_);
return v_res_588_;
}
}
lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* v_x_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_589_, v_a_591_);
return v___x_597_;
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_collectLevelAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_589_ = stack[0].m_obj;
lean_object* v_a_590_ = stack[1].m_obj;
lean_object* v_a_591_ = stack[2].m_obj;
lean_object* v_a_592_ = stack[3].m_obj;
lean_object* v_a_593_ = stack[4].m_obj;
lean_object* v_a_594_ = stack[5].m_obj;
lean_object* v_a_595_ = stack[6].m_obj;
lean_object* v_res_598_;
v_res_598_ = l_Lean_Meta_Closure_collectLevelAux(v_x_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
stack->m_obj
 = v_res_598_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* v_x_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Meta_Closure_collectLevelAux(v_x_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(lean_object* v_00_u03b2_608_, lean_object* v_m_609_, lean_object* v_a_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_609_, v_a_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object* v_00_u03b2_612_, lean_object* v_m_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(v_00_u03b2_612_, v_m_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec_ref(v_m_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2(lean_object* v_00_u03b2_616_, lean_object* v_m_617_, lean_object* v_a_618_, lean_object* v_b_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_m_617_, v_a_618_, v_b_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(lean_object* v_00_u03b2_621_, lean_object* v_a_622_, lean_object* v_x_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_622_, v_x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___boxed(lean_object* v_00_u03b2_625_, lean_object* v_a_626_, lean_object* v_x_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(v_00_u03b2_625_, v_a_626_, v_x_627_);
lean_dec(v_x_627_);
lean_dec(v_a_626_);
return v_res_628_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(lean_object* v_00_u03b2_629_, lean_object* v_a_630_, lean_object* v_x_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_630_, v_x_631_);
return v___x_632_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_630_ = stack[1].m_obj;
lean_object* v_x_631_ = stack[2].m_obj;
uint8_t v_res_633_;
v_res_633_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(lean_box(0), v_a_630_, v_x_631_);
stack->m_num = v_res_633_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___boxed(lean_object* v_00_u03b2_634_, lean_object* v_a_635_, lean_object* v_x_636_){
_start:
{
uint8_t v_res_637_; lean_object* v_r_638_; 
v_res_637_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(v_00_u03b2_634_, v_a_635_, v_x_636_);
lean_dec(v_x_636_);
lean_dec(v_a_635_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4(lean_object* v_00_u03b2_639_, lean_object* v_data_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_data_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5(lean_object* v_00_u03b2_642_, lean_object* v_a_643_, lean_object* v_b_644_, lean_object* v_x_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_643_, v_b_644_, v_x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_647_, lean_object* v_i_648_, lean_object* v_source_649_, lean_object* v_target_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v_i_648_, v_source_649_, v_target_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_x_653_, v_x_654_);
return v___x_655_;
}
}
lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object* v_u_656_, lean_object* v_a_657_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = l_Lean_Level_hasMVar(v_u_656_);
if (v___x_702_ == 0)
{
uint8_t v___x_703_; 
v___x_703_ = l_Lean_Level_hasParam(v_u_656_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v_u_656_);
return v___x_704_;
}
else
{
goto v___jp_659_;
}
}
else
{
goto v___jp_659_;
}
v___jp_659_:
{
lean_object* v___x_660_; lean_object* v_visitedLevel_661_; lean_object* v___x_662_; 
v___x_660_ = lean_st_ref_get(v_a_657_);
v_visitedLevel_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc_ref(v_visitedLevel_661_);
lean_dec(v___x_660_);
v___x_662_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_661_, v_u_656_);
lean_dec_ref(v_visitedLevel_661_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v___x_663_; 
lean_inc(v_u_656_);
v___x_663_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_u_656_, v_a_657_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_693_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_693_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_693_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_693_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v_visitedLevel_669_; lean_object* v_visitedExpr_670_; lean_object* v_levelParams_671_; lean_object* v_nextLevelIdx_672_; lean_object* v_levelArgs_673_; lean_object* v_newLocalDecls_674_; lean_object* v_newLocalDeclsForMVars_675_; lean_object* v_newLetDecls_676_; lean_object* v_nextExprIdx_677_; lean_object* v_exprMVarArgs_678_; lean_object* v_exprFVarArgs_679_; lean_object* v_toProcess_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_692_; 
v___x_668_ = lean_st_ref_take(v_a_657_);
v_visitedLevel_669_ = lean_ctor_get(v___x_668_, 0);
v_visitedExpr_670_ = lean_ctor_get(v___x_668_, 1);
v_levelParams_671_ = lean_ctor_get(v___x_668_, 2);
v_nextLevelIdx_672_ = lean_ctor_get(v___x_668_, 3);
v_levelArgs_673_ = lean_ctor_get(v___x_668_, 4);
v_newLocalDecls_674_ = lean_ctor_get(v___x_668_, 5);
v_newLocalDeclsForMVars_675_ = lean_ctor_get(v___x_668_, 6);
v_newLetDecls_676_ = lean_ctor_get(v___x_668_, 7);
v_nextExprIdx_677_ = lean_ctor_get(v___x_668_, 8);
v_exprMVarArgs_678_ = lean_ctor_get(v___x_668_, 9);
v_exprFVarArgs_679_ = lean_ctor_get(v___x_668_, 10);
v_toProcess_680_ = lean_ctor_get(v___x_668_, 11);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_692_ == 0)
{
v___x_682_ = v___x_668_;
v_isShared_683_ = v_isSharedCheck_692_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_toProcess_680_);
lean_inc(v_exprFVarArgs_679_);
lean_inc(v_exprMVarArgs_678_);
lean_inc(v_nextExprIdx_677_);
lean_inc(v_newLetDecls_676_);
lean_inc(v_newLocalDeclsForMVars_675_);
lean_inc(v_newLocalDecls_674_);
lean_inc(v_levelArgs_673_);
lean_inc(v_nextLevelIdx_672_);
lean_inc(v_levelParams_671_);
lean_inc(v_visitedExpr_670_);
lean_inc(v_visitedLevel_669_);
lean_dec(v___x_668_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_692_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
lean_inc(v_a_664_);
v___x_684_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_669_, v_u_656_, v_a_664_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_684_);
v___x_686_ = v___x_682_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_visitedExpr_670_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_levelParams_671_);
lean_ctor_set(v_reuseFailAlloc_691_, 3, v_nextLevelIdx_672_);
lean_ctor_set(v_reuseFailAlloc_691_, 4, v_levelArgs_673_);
lean_ctor_set(v_reuseFailAlloc_691_, 5, v_newLocalDecls_674_);
lean_ctor_set(v_reuseFailAlloc_691_, 6, v_newLocalDeclsForMVars_675_);
lean_ctor_set(v_reuseFailAlloc_691_, 7, v_newLetDecls_676_);
lean_ctor_set(v_reuseFailAlloc_691_, 8, v_nextExprIdx_677_);
lean_ctor_set(v_reuseFailAlloc_691_, 9, v_exprMVarArgs_678_);
lean_ctor_set(v_reuseFailAlloc_691_, 10, v_exprFVarArgs_679_);
lean_ctor_set(v_reuseFailAlloc_691_, 11, v_toProcess_680_);
v___x_686_ = v_reuseFailAlloc_691_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = lean_st_ref_put(v_a_657_, v___x_686_);
if (v_isShared_667_ == 0)
{
v___x_689_ = v___x_666_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_664_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
else
{
lean_dec(v_u_656_);
return v___x_663_;
}
}
else
{
lean_object* v_val_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec(v_u_656_);
v_val_694_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_662_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_val_694_);
lean_dec(v___x_662_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set_tag(v___x_696_, 0);
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_val_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_collectLevel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_656_ = stack[0].m_obj;
lean_object* v_a_657_ = stack[1].m_obj;
lean_object* v_res_705_;
v_res_705_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_656_, v_a_657_);
stack->m_obj
 = v_res_705_;
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
lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* v_u_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_710_, v_a_712_);
return v___x_718_;
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_collectLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_710_ = stack[0].m_obj;
lean_object* v_a_711_ = stack[1].m_obj;
lean_object* v_a_712_ = stack[2].m_obj;
lean_object* v_a_713_ = stack[3].m_obj;
lean_object* v_a_714_ = stack[4].m_obj;
lean_object* v_a_715_ = stack[5].m_obj;
lean_object* v_a_716_ = stack[6].m_obj;
lean_object* v_res_719_;
v_res_719_ = l_Lean_Meta_Closure_collectLevel(v_u_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
stack->m_obj
 = v_res_719_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* v_u_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Meta_Closure_collectLevel(v_u_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
return v_res_728_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object* v_e_729_, lean_object* v___y_730_){
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
v___x_749_ = lean_st_ref_put(v___y_730_, v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v_fst_737_);
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_729_ = stack[0].m_obj;
lean_object* v___y_730_ = stack[1].m_obj;
lean_object* v_res_754_;
v_res_754_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_729_, v___y_730_);
stack->m_obj
 = v_res_754_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object* v_e_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_755_, v___y_756_);
lean_dec(v___y_756_);
return v_res_758_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(lean_object* v_e_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_759_, v___y_763_);
return v___x_767_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_759_ = stack[0].m_obj;
lean_object* v___y_760_ = stack[1].m_obj;
lean_object* v___y_761_ = stack[2].m_obj;
lean_object* v___y_762_ = stack[3].m_obj;
lean_object* v___y_763_ = stack[4].m_obj;
lean_object* v___y_764_ = stack[5].m_obj;
lean_object* v___y_765_ = stack[6].m_obj;
lean_object* v_res_768_;
v_res_768_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(v_e_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
stack->m_obj
 = v_res_768_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object* v_e_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(v_e_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
return v_res_777_;
}
}
lean_object* l_Lean_Meta_Closure_preprocess(lean_object* v_e_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_786_; uint8_t v_zetaDelta_787_; 
v___x_786_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_778_, v_a_782_);
v_zetaDelta_787_ = lean_ctor_get_uint8(v_a_779_, 0);
if (v_zetaDelta_787_ == 0)
{
uint8_t v_hasLetDecls_788_; 
v_hasLetDecls_788_ = lean_ctor_get_uint8(v_a_779_, 1);
if (v_hasLetDecls_788_ == 0)
{
return v___x_786_;
}
else
{
lean_object* v_a_789_; uint8_t v___x_790_; lean_object* v___x_791_; 
v_a_789_ = lean_ctor_get(v___x_786_, 0);
lean_inc_n(v_a_789_, 2);
lean_dec_ref(v___x_786_);
v___x_790_ = 0;
v___x_791_ = l_Lean_Meta_check(v_a_789_, v___x_790_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v___x_791_, 0);
lean_dec(v_unused_799_);
v___x_793_ = v___x_791_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_dec(v___x_791_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v_a_789_);
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_789_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v_a_789_);
v_a_800_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_791_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_791_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
else
{
return v___x_786_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_preprocess_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_778_ = stack[0].m_obj;
lean_object* v_a_779_ = stack[1].m_obj;
lean_object* v_a_780_ = stack[2].m_obj;
lean_object* v_a_781_ = stack[3].m_obj;
lean_object* v_a_782_ = stack[4].m_obj;
lean_object* v_a_783_ = stack[5].m_obj;
lean_object* v_a_784_ = stack[6].m_obj;
lean_object* v_res_808_;
v_res_808_ = l_Lean_Meta_Closure_preprocess(v_e_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
stack->m_obj
 = v_res_808_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* v_e_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_Meta_Closure_preprocess(v_e_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_817_;
}
}
lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; lean_object* v_nextExprIdx_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_visitedLevel_828_; lean_object* v_visitedExpr_829_; lean_object* v_levelParams_830_; lean_object* v_nextLevelIdx_831_; lean_object* v_levelArgs_832_; lean_object* v_newLocalDecls_833_; lean_object* v_newLocalDeclsForMVars_834_; lean_object* v_newLetDecls_835_; lean_object* v_nextExprIdx_836_; lean_object* v_exprMVarArgs_837_; lean_object* v_exprFVarArgs_838_; lean_object* v_toProcess_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_850_; 
v___x_823_ = lean_st_ref_get(v_a_821_);
v_nextExprIdx_824_ = lean_ctor_get(v___x_823_, 8);
lean_inc(v_nextExprIdx_824_);
lean_dec(v___x_823_);
v___x_825_ = ((lean_object*)(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1));
v___x_826_ = lean_name_append_index_after(v___x_825_, v_nextExprIdx_824_);
v___x_827_ = lean_st_ref_take(v_a_821_);
v_visitedLevel_828_ = lean_ctor_get(v___x_827_, 0);
v_visitedExpr_829_ = lean_ctor_get(v___x_827_, 1);
v_levelParams_830_ = lean_ctor_get(v___x_827_, 2);
v_nextLevelIdx_831_ = lean_ctor_get(v___x_827_, 3);
v_levelArgs_832_ = lean_ctor_get(v___x_827_, 4);
v_newLocalDecls_833_ = lean_ctor_get(v___x_827_, 5);
v_newLocalDeclsForMVars_834_ = lean_ctor_get(v___x_827_, 6);
v_newLetDecls_835_ = lean_ctor_get(v___x_827_, 7);
v_nextExprIdx_836_ = lean_ctor_get(v___x_827_, 8);
v_exprMVarArgs_837_ = lean_ctor_get(v___x_827_, 9);
v_exprFVarArgs_838_ = lean_ctor_get(v___x_827_, 10);
v_toProcess_839_ = lean_ctor_get(v___x_827_, 11);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_850_ == 0)
{
v___x_841_ = v___x_827_;
v_isShared_842_ = v_isSharedCheck_850_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_toProcess_839_);
lean_inc(v_exprFVarArgs_838_);
lean_inc(v_exprMVarArgs_837_);
lean_inc(v_nextExprIdx_836_);
lean_inc(v_newLetDecls_835_);
lean_inc(v_newLocalDeclsForMVars_834_);
lean_inc(v_newLocalDecls_833_);
lean_inc(v_levelArgs_832_);
lean_inc(v_nextLevelIdx_831_);
lean_inc(v_levelParams_830_);
lean_inc(v_visitedExpr_829_);
lean_inc(v_visitedLevel_828_);
lean_dec(v___x_827_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_850_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_add(v_nextExprIdx_836_, v___x_843_);
lean_dec(v_nextExprIdx_836_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 8, v___x_844_);
v___x_846_ = v___x_841_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_visitedLevel_828_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_visitedExpr_829_);
lean_ctor_set(v_reuseFailAlloc_849_, 2, v_levelParams_830_);
lean_ctor_set(v_reuseFailAlloc_849_, 3, v_nextLevelIdx_831_);
lean_ctor_set(v_reuseFailAlloc_849_, 4, v_levelArgs_832_);
lean_ctor_set(v_reuseFailAlloc_849_, 5, v_newLocalDecls_833_);
lean_ctor_set(v_reuseFailAlloc_849_, 6, v_newLocalDeclsForMVars_834_);
lean_ctor_set(v_reuseFailAlloc_849_, 7, v_newLetDecls_835_);
lean_ctor_set(v_reuseFailAlloc_849_, 8, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_849_, 9, v_exprMVarArgs_837_);
lean_ctor_set(v_reuseFailAlloc_849_, 10, v_exprFVarArgs_838_);
lean_ctor_set(v_reuseFailAlloc_849_, 11, v_toProcess_839_);
v___x_846_ = v_reuseFailAlloc_849_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_st_ref_put(v_a_821_, v___x_846_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_826_);
return v___x_848_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_mkNextUserName___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_821_ = stack[0].m_obj;
lean_object* v_res_851_;
v_res_851_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_821_);
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_852_);
lean_dec(v_a_852_);
return v_res_854_;
}
}
lean_object* l_Lean_Meta_Closure_mkNextUserName(lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_856_);
return v___x_862_;
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_mkNextUserName_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_855_ = stack[0].m_obj;
lean_object* v_a_856_ = stack[1].m_obj;
lean_object* v_a_857_ = stack[2].m_obj;
lean_object* v_a_858_ = stack[3].m_obj;
lean_object* v_a_859_ = stack[4].m_obj;
lean_object* v_a_860_ = stack[5].m_obj;
lean_object* v_res_863_;
v_res_863_ = l_Lean_Meta_Closure_mkNextUserName(v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
stack->m_obj
 = v_res_863_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Meta_Closure_mkNextUserName(v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
return v_res_871_;
}
}
lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object* v_elem_872_, lean_object* v_a_873_){
_start:
{
lean_object* v___x_875_; lean_object* v_visitedLevel_876_; lean_object* v_visitedExpr_877_; lean_object* v_levelParams_878_; lean_object* v_nextLevelIdx_879_; lean_object* v_levelArgs_880_; lean_object* v_newLocalDecls_881_; lean_object* v_newLocalDeclsForMVars_882_; lean_object* v_newLetDecls_883_; lean_object* v_nextExprIdx_884_; lean_object* v_exprMVarArgs_885_; lean_object* v_exprFVarArgs_886_; lean_object* v_toProcess_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_898_; 
v___x_875_ = lean_st_ref_take(v_a_873_);
v_visitedLevel_876_ = lean_ctor_get(v___x_875_, 0);
v_visitedExpr_877_ = lean_ctor_get(v___x_875_, 1);
v_levelParams_878_ = lean_ctor_get(v___x_875_, 2);
v_nextLevelIdx_879_ = lean_ctor_get(v___x_875_, 3);
v_levelArgs_880_ = lean_ctor_get(v___x_875_, 4);
v_newLocalDecls_881_ = lean_ctor_get(v___x_875_, 5);
v_newLocalDeclsForMVars_882_ = lean_ctor_get(v___x_875_, 6);
v_newLetDecls_883_ = lean_ctor_get(v___x_875_, 7);
v_nextExprIdx_884_ = lean_ctor_get(v___x_875_, 8);
v_exprMVarArgs_885_ = lean_ctor_get(v___x_875_, 9);
v_exprFVarArgs_886_ = lean_ctor_get(v___x_875_, 10);
v_toProcess_887_ = lean_ctor_get(v___x_875_, 11);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_898_ == 0)
{
v___x_889_ = v___x_875_;
v_isShared_890_ = v_isSharedCheck_898_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_toProcess_887_);
lean_inc(v_exprFVarArgs_886_);
lean_inc(v_exprMVarArgs_885_);
lean_inc(v_nextExprIdx_884_);
lean_inc(v_newLetDecls_883_);
lean_inc(v_newLocalDeclsForMVars_882_);
lean_inc(v_newLocalDecls_881_);
lean_inc(v_levelArgs_880_);
lean_inc(v_nextLevelIdx_879_);
lean_inc(v_levelParams_878_);
lean_inc(v_visitedExpr_877_);
lean_inc(v_visitedLevel_876_);
lean_dec(v___x_875_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_898_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_891_ = lean_box(0);
v___x_892_ = lean_array_push(v_toProcess_887_, v_elem_872_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 11, v___x_892_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_visitedLevel_876_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_visitedExpr_877_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_levelParams_878_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v_nextLevelIdx_879_);
lean_ctor_set(v_reuseFailAlloc_897_, 4, v_levelArgs_880_);
lean_ctor_set(v_reuseFailAlloc_897_, 5, v_newLocalDecls_881_);
lean_ctor_set(v_reuseFailAlloc_897_, 6, v_newLocalDeclsForMVars_882_);
lean_ctor_set(v_reuseFailAlloc_897_, 7, v_newLetDecls_883_);
lean_ctor_set(v_reuseFailAlloc_897_, 8, v_nextExprIdx_884_);
lean_ctor_set(v_reuseFailAlloc_897_, 9, v_exprMVarArgs_885_);
lean_ctor_set(v_reuseFailAlloc_897_, 10, v_exprFVarArgs_886_);
lean_ctor_set(v_reuseFailAlloc_897_, 11, v___x_892_);
v___x_894_ = v_reuseFailAlloc_897_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_st_ref_put(v_a_873_, v___x_894_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_891_);
return v___x_896_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_pushToProcess___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_elem_872_ = stack[0].m_obj;
lean_object* v_a_873_ = stack[1].m_obj;
lean_object* v_res_899_;
v_res_899_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_872_, v_a_873_);
stack->m_obj
 = v_res_899_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object* v_elem_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_900_, v_a_901_);
lean_dec(v_a_901_);
return v_res_903_;
}
}
lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* v_elem_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_904_, v_a_906_);
return v___x_912_;
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_pushToProcess_0interp(lean_interpreter_value* stack)
{
lean_object* v_elem_904_ = stack[0].m_obj;
lean_object* v_a_905_ = stack[1].m_obj;
lean_object* v_a_906_ = stack[2].m_obj;
lean_object* v_a_907_ = stack[3].m_obj;
lean_object* v_a_908_ = stack[4].m_obj;
lean_object* v_a_909_ = stack[5].m_obj;
lean_object* v_a_910_ = stack[6].m_obj;
lean_object* v_res_913_;
v_res_913_ = l_Lean_Meta_Closure_pushToProcess(v_elem_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
stack->m_obj
 = v_res_913_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* v_elem_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Meta_Closure_pushToProcess(v_elem_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
return v_res_922_;
}
}
lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(lean_object* v_mvarId_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; lean_object* v_mctx_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_926_ = lean_st_ref_get(v___y_924_);
v_mctx_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc_ref(v_mctx_927_);
lean_dec(v___x_926_);
v___x_928_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_927_, v_mvarId_923_);
lean_dec_ref(v_mctx_927_);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT void l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_923_ = stack[0].m_obj;
lean_object* v___y_924_ = stack[1].m_obj;
lean_object* v_res_930_;
v_res_930_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_923_, v___y_924_);
stack->m_obj
 = v_res_930_;
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(lean_object* v_mvarId_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec(v_mvarId_931_);
return v_res_934_;
}
}
lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(lean_object* v_mvarId_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_935_, v___y_939_);
return v___x_943_;
}
}
LEAN_EXPORT void l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_935_ = stack[0].m_obj;
lean_object* v___y_936_ = stack[1].m_obj;
lean_object* v___y_937_ = stack[2].m_obj;
lean_object* v___y_938_ = stack[3].m_obj;
lean_object* v___y_939_ = stack[4].m_obj;
lean_object* v___y_940_ = stack[5].m_obj;
lean_object* v___y_941_ = stack[6].m_obj;
lean_object* v_res_944_;
v_res_944_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(v_mvarId_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
stack->m_obj
 = v_res_944_;
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object* v_mvarId_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(v_mvarId_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v_mvarId_945_);
return v_res_953_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(lean_object* v_k_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v_b_957_, lean_object* v_c_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; 
lean_inc(v___y_962_);
lean_inc_ref(v___y_961_);
lean_inc(v___y_960_);
lean_inc_ref(v___y_959_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
v___x_964_ = lean_apply_9(v_k_954_, v_b_957_, v_c_958_, v___y_955_, v___y_956_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, lean_box(0));
return v___x_964_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_954_ = stack[0].m_obj;
lean_object* v___y_955_ = stack[1].m_obj;
lean_object* v___y_956_ = stack[2].m_obj;
lean_object* v_b_957_ = stack[3].m_obj;
lean_object* v_c_958_ = stack[4].m_obj;
lean_object* v___y_959_ = stack[5].m_obj;
lean_object* v___y_960_ = stack[6].m_obj;
lean_object* v___y_961_ = stack[7].m_obj;
lean_object* v___y_962_ = stack[8].m_obj;
lean_object* v_res_965_;
v_res_965_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(v_k_954_, v___y_955_, v___y_956_, v_b_957_, v_c_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
stack->m_obj
 = v_res_965_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed(lean_object* v_k_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v_b_969_, lean_object* v_c_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(v_k_966_, v___y_967_, v___y_968_, v_b_969_, v_c_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_976_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object* v_type_977_, lean_object* v_maxFVars_x3f_978_, lean_object* v_k_979_, uint8_t v_cleanupAnnotations_980_, uint8_t v_whnfType_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___f_989_; lean_object* v___x_990_; 
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
v___f_989_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_989_, 0, v_k_979_);
lean_closure_set(v___f_989_, 1, v___y_982_);
lean_closure_set(v___f_989_, 2, v___y_983_);
v___x_990_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_977_, v_maxFVars_x3f_978_, v___f_989_, v_cleanupAnnotations_980_, v_whnfType_981_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_990_) == 0)
{
return v___x_990_;
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_977_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_978_ = stack[1].m_obj;
lean_object* v_k_979_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_980_ = stack[3].m_num;
uint8_t v_whnfType_981_ = stack[4].m_num;
lean_object* v___y_982_ = stack[5].m_obj;
lean_object* v___y_983_ = stack[6].m_obj;
lean_object* v___y_984_ = stack[7].m_obj;
lean_object* v___y_985_ = stack[8].m_obj;
lean_object* v___y_986_ = stack[9].m_obj;
lean_object* v___y_987_ = stack[10].m_obj;
lean_object* v_res_999_;
v_res_999_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_977_, v_maxFVars_x3f_978_, v_k_979_, v_cleanupAnnotations_980_, v_whnfType_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(lean_object* v_type_1000_, lean_object* v_maxFVars_x3f_1001_, lean_object* v_k_1002_, lean_object* v_cleanupAnnotations_1003_, lean_object* v_whnfType_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1012_; uint8_t v_whnfType_boxed_1013_; lean_object* v_res_1014_; 
v_cleanupAnnotations_boxed_1012_ = lean_unbox(v_cleanupAnnotations_1003_);
v_whnfType_boxed_1013_ = lean_unbox(v_whnfType_1004_);
v_res_1014_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1000_, v_maxFVars_x3f_1001_, v_k_1002_, v_cleanupAnnotations_boxed_1012_, v_whnfType_boxed_1013_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1014_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_object* v_00_u03b1_1015_, lean_object* v_type_1016_, lean_object* v_maxFVars_x3f_1017_, lean_object* v_k_1018_, uint8_t v_cleanupAnnotations_1019_, uint8_t v_whnfType_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1016_, v_maxFVars_x3f_1017_, v_k_1018_, v_cleanupAnnotations_1019_, v_whnfType_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1016_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_1017_ = stack[2].m_obj;
lean_object* v_k_1018_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_1019_ = stack[4].m_num;
uint8_t v_whnfType_1020_ = stack[5].m_num;
lean_object* v___y_1021_ = stack[6].m_obj;
lean_object* v___y_1022_ = stack[7].m_obj;
lean_object* v___y_1023_ = stack[8].m_obj;
lean_object* v___y_1024_ = stack[9].m_obj;
lean_object* v___y_1025_ = stack[10].m_obj;
lean_object* v___y_1026_ = stack[11].m_obj;
lean_object* v_res_1029_;
v_res_1029_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_box(0), v_type_1016_, v_maxFVars_x3f_1017_, v_k_1018_, v_cleanupAnnotations_1019_, v_whnfType_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
stack->m_obj
 = v_res_1029_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(lean_object* v_00_u03b1_1030_, lean_object* v_type_1031_, lean_object* v_maxFVars_x3f_1032_, lean_object* v_k_1033_, lean_object* v_cleanupAnnotations_1034_, lean_object* v_whnfType_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1043_; uint8_t v_whnfType_boxed_1044_; lean_object* v_res_1045_; 
v_cleanupAnnotations_boxed_1043_ = lean_unbox(v_cleanupAnnotations_1034_);
v_whnfType_boxed_1044_ = lean_unbox(v_whnfType_1035_);
v_res_1045_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(v_00_u03b1_1030_, v_type_1031_, v_maxFVars_x3f_1032_, v_k_1033_, v_cleanupAnnotations_boxed_1043_, v_whnfType_boxed_1044_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object* v_a_1046_, lean_object* v_x_1047_){
_start:
{
if (lean_obj_tag(v_x_1047_) == 0)
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_box(0);
return v___x_1048_;
}
else
{
lean_object* v_key_1049_; lean_object* v_value_1050_; lean_object* v_tail_1051_; uint8_t v___x_1052_; 
v_key_1049_ = lean_ctor_get(v_x_1047_, 0);
v_value_1050_ = lean_ctor_get(v_x_1047_, 1);
v_tail_1051_ = lean_ctor_get(v_x_1047_, 2);
v___x_1052_ = l_Lean_ExprStructEq_beq(v_key_1049_, v_a_1046_);
if (v___x_1052_ == 0)
{
v_x_1047_ = v_tail_1051_;
goto _start;
}
else
{
lean_object* v___x_1054_; 
lean_inc(v_value_1050_);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_value_1050_);
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_1055_, lean_object* v_x_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1055_, v_x_1056_);
lean_dec(v_x_1056_);
lean_dec_ref(v_a_1055_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object* v_m_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_buckets_1060_; lean_object* v___x_1061_; uint64_t v___x_1062_; uint64_t v___x_1063_; uint64_t v___x_1064_; uint64_t v_fold_1065_; uint64_t v___x_1066_; uint64_t v___x_1067_; uint64_t v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_buckets_1060_ = lean_ctor_get(v_m_1058_, 1);
v___x_1061_ = lean_array_get_size(v_buckets_1060_);
v___x_1062_ = l_Lean_ExprStructEq_hash(v_a_1059_);
v___x_1063_ = 32ULL;
v___x_1064_ = lean_uint64_shift_right(v___x_1062_, v___x_1063_);
v_fold_1065_ = lean_uint64_xor(v___x_1062_, v___x_1064_);
v___x_1066_ = 16ULL;
v___x_1067_ = lean_uint64_shift_right(v_fold_1065_, v___x_1066_);
v___x_1068_ = lean_uint64_xor(v_fold_1065_, v___x_1067_);
v___x_1069_ = lean_uint64_to_usize(v___x_1068_);
v___x_1070_ = lean_usize_of_nat(v___x_1061_);
v___x_1071_ = ((size_t)1ULL);
v___x_1072_ = lean_usize_sub(v___x_1070_, v___x_1071_);
v___x_1073_ = lean_usize_land(v___x_1069_, v___x_1072_);
v___x_1074_ = lean_array_uget_borrowed(v_buckets_1060_, v___x_1073_);
v___x_1075_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1059_, v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object* v_m_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1076_, v_a_1077_);
lean_dec_ref(v_a_1077_);
lean_dec_ref(v_m_1076_);
return v_res_1078_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v___y_1081_){
_start:
{
if (lean_obj_tag(v_x_1079_) == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = l_List_reverse___redArg(v_x_1080_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
else
{
lean_object* v_head_1085_; lean_object* v_tail_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1104_; 
v_head_1085_ = lean_ctor_get(v_x_1079_, 0);
v_tail_1086_ = lean_ctor_get(v_x_1079_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_x_1079_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1088_ = v_x_1079_;
v_isShared_1089_ = v_isSharedCheck_1104_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_tail_1086_);
lean_inc(v_head_1085_);
lean_dec(v_x_1079_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1104_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Meta_Closure_collectLevel___redArg(v_head_1085_, v___y_1081_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v_x_1080_);
lean_ctor_set(v___x_1088_, 0, v_a_1091_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1091_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_x_1080_);
v___x_1093_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v_x_1079_ = v_tail_1086_;
v_x_1080_ = v___x_1093_;
goto _start;
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_del_object(v___x_1088_);
lean_dec(v_tail_1086_);
lean_dec(v_x_1080_);
v_a_1096_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1090_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1090_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1079_ = stack[0].m_obj;
lean_object* v_x_1080_ = stack[1].m_obj;
lean_object* v___y_1081_ = stack[2].m_obj;
lean_object* v_res_1105_;
v_res_1105_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1079_, v_x_1080_, v___y_1081_);
stack->m_obj
 = v_res_1105_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1106_, v_x_1107_, v___y_1108_);
lean_dec(v___y_1108_);
return v_res_1110_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v_ngen_1114_; lean_object* v_namePrefix_1115_; lean_object* v_idx_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1146_; 
v___x_1113_ = lean_st_ref_get(v___y_1111_);
v_ngen_1114_ = lean_ctor_get(v___x_1113_, 2);
lean_inc_ref(v_ngen_1114_);
lean_dec(v___x_1113_);
v_namePrefix_1115_ = lean_ctor_get(v_ngen_1114_, 0);
v_idx_1116_ = lean_ctor_get(v_ngen_1114_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_ngen_1114_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1118_ = v_ngen_1114_;
v_isShared_1119_ = v_isSharedCheck_1146_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_idx_1116_);
lean_inc(v_namePrefix_1115_);
lean_dec(v_ngen_1114_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1146_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v_r_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
lean_inc(v_idx_1116_);
lean_inc(v_namePrefix_1115_);
v_r_1120_ = l_Lean_Name_num___override(v_namePrefix_1115_, v_idx_1116_);
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v_idx_1116_, v___x_1121_);
lean_dec(v_idx_1116_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v___x_1122_);
v___x_1124_ = v___x_1118_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_namePrefix_1115_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; lean_object* v_env_1126_; lean_object* v_nextMacroScope_1127_; lean_object* v_auxDeclNGen_1128_; lean_object* v_traceState_1129_; lean_object* v_cache_1130_; lean_object* v_recordedDeps_1131_; lean_object* v_messages_1132_; lean_object* v_infoState_1133_; lean_object* v_snapshotTasks_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1143_; 
v___x_1125_ = lean_st_ref_take(v___y_1111_);
v_env_1126_ = lean_ctor_get(v___x_1125_, 0);
v_nextMacroScope_1127_ = lean_ctor_get(v___x_1125_, 1);
v_auxDeclNGen_1128_ = lean_ctor_get(v___x_1125_, 3);
v_traceState_1129_ = lean_ctor_get(v___x_1125_, 4);
v_cache_1130_ = lean_ctor_get(v___x_1125_, 5);
v_recordedDeps_1131_ = lean_ctor_get(v___x_1125_, 6);
v_messages_1132_ = lean_ctor_get(v___x_1125_, 7);
v_infoState_1133_ = lean_ctor_get(v___x_1125_, 8);
v_snapshotTasks_1134_ = lean_ctor_get(v___x_1125_, 9);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v___x_1125_, 2);
lean_dec(v_unused_1144_);
v___x_1136_ = v___x_1125_;
v_isShared_1137_ = v_isSharedCheck_1143_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_snapshotTasks_1134_);
lean_inc(v_infoState_1133_);
lean_inc(v_messages_1132_);
lean_inc(v_recordedDeps_1131_);
lean_inc(v_cache_1130_);
lean_inc(v_traceState_1129_);
lean_inc(v_auxDeclNGen_1128_);
lean_inc(v_nextMacroScope_1127_);
lean_inc(v_env_1126_);
lean_dec(v___x_1125_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1143_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 2, v___x_1124_);
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_env_1126_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_nextMacroScope_1127_);
lean_ctor_set(v_reuseFailAlloc_1142_, 2, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1142_, 3, v_auxDeclNGen_1128_);
lean_ctor_set(v_reuseFailAlloc_1142_, 4, v_traceState_1129_);
lean_ctor_set(v_reuseFailAlloc_1142_, 5, v_cache_1130_);
lean_ctor_set(v_reuseFailAlloc_1142_, 6, v_recordedDeps_1131_);
lean_ctor_set(v_reuseFailAlloc_1142_, 7, v_messages_1132_);
lean_ctor_set(v_reuseFailAlloc_1142_, 8, v_infoState_1133_);
lean_ctor_set(v_reuseFailAlloc_1142_, 9, v_snapshotTasks_1134_);
v___x_1139_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_st_ref_put(v___y_1111_, v___x_1139_);
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_r_1120_);
return v___x_1141_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1111_ = stack[0].m_obj;
lean_object* v_res_1147_;
v_res_1147_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1111_);
stack->m_obj
 = v_res_1147_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg___boxed(lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1148_);
lean_dec(v___y_1148_);
return v_res_1150_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v___x_1158_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1156_);
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1151_ = stack[0].m_obj;
lean_object* v___y_1152_ = stack[1].m_obj;
lean_object* v___y_1153_ = stack[2].m_obj;
lean_object* v___y_1154_ = stack[3].m_obj;
lean_object* v___y_1155_ = stack[4].m_obj;
lean_object* v___y_1156_ = stack[5].m_obj;
lean_object* v_res_1167_;
v_res_1167_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
stack->m_obj
 = v_res_1167_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1175_;
}
}
lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object* v_e_1176_, lean_object* v_args_1177_, lean_object* v_x_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; uint8_t v___x_1187_; uint8_t v___x_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; 
v___x_1186_ = l_Lean_mkAppN(v_e_1176_, v_args_1177_);
v___x_1187_ = 0;
v___x_1188_ = 1;
v___x_1189_ = 1;
v___x_1190_ = l_Lean_Meta_mkLambdaFVars(v_args_1177_, v___x_1186_, v___x_1187_, v___x_1188_, v___x_1187_, v___x_1188_, v___x_1189_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
return v___x_1190_;
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_collectExprAux___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1176_ = stack[0].m_obj;
lean_object* v_args_1177_ = stack[1].m_obj;
lean_object* v_x_1178_ = stack[2].m_obj;
lean_object* v___y_1179_ = stack[3].m_obj;
lean_object* v___y_1180_ = stack[4].m_obj;
lean_object* v___y_1181_ = stack[5].m_obj;
lean_object* v___y_1182_ = stack[6].m_obj;
lean_object* v___y_1183_ = stack[7].m_obj;
lean_object* v___y_1184_ = stack[8].m_obj;
lean_object* v_res_1191_;
v_res_1191_ = l_Lean_Meta_Closure_collectExprAux___lam__1(v_e_1176_, v_args_1177_, v_x_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
stack->m_obj
 = v_res_1191_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object* v_e_1192_, lean_object* v_args_1193_, lean_object* v_x_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Meta_Closure_collectExprAux___lam__1(v_e_1192_, v_args_1193_, v_x_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v_x_1194_);
lean_dec_ref(v_args_1193_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_x_1203_, lean_object* v_x_1204_){
_start:
{
if (lean_obj_tag(v_x_1204_) == 0)
{
return v_x_1203_;
}
else
{
lean_object* v_key_1205_; lean_object* v_value_1206_; lean_object* v_tail_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1230_; 
v_key_1205_ = lean_ctor_get(v_x_1204_, 0);
v_value_1206_ = lean_ctor_get(v_x_1204_, 1);
v_tail_1207_ = lean_ctor_get(v_x_1204_, 2);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_x_1204_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1209_ = v_x_1204_;
v_isShared_1210_ = v_isSharedCheck_1230_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_tail_1207_);
lean_inc(v_value_1206_);
lean_inc(v_key_1205_);
lean_dec(v_x_1204_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1230_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; uint64_t v___x_1212_; uint64_t v___x_1213_; uint64_t v___x_1214_; uint64_t v_fold_1215_; uint64_t v___x_1216_; uint64_t v___x_1217_; uint64_t v___x_1218_; size_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1211_ = lean_array_get_size(v_x_1203_);
v___x_1212_ = l_Lean_ExprStructEq_hash(v_key_1205_);
v___x_1213_ = 32ULL;
v___x_1214_ = lean_uint64_shift_right(v___x_1212_, v___x_1213_);
v_fold_1215_ = lean_uint64_xor(v___x_1212_, v___x_1214_);
v___x_1216_ = 16ULL;
v___x_1217_ = lean_uint64_shift_right(v_fold_1215_, v___x_1216_);
v___x_1218_ = lean_uint64_xor(v_fold_1215_, v___x_1217_);
v___x_1219_ = lean_uint64_to_usize(v___x_1218_);
v___x_1220_ = lean_usize_of_nat(v___x_1211_);
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_sub(v___x_1220_, v___x_1221_);
v___x_1223_ = lean_usize_land(v___x_1219_, v___x_1222_);
v___x_1224_ = lean_array_uget_borrowed(v_x_1203_, v___x_1223_);
lean_inc(v___x_1224_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 2, v___x_1224_);
v___x_1226_ = v___x_1209_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_key_1205_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_value_1206_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_array_uset(v_x_1203_, v___x_1223_, v___x_1226_);
v_x_1203_ = v___x_1227_;
v_x_1204_ = v_tail_1207_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(lean_object* v_i_1231_, lean_object* v_source_1232_, lean_object* v_target_1233_){
_start:
{
lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = lean_array_get_size(v_source_1232_);
v___x_1235_ = lean_nat_dec_lt(v_i_1231_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_dec_ref(v_source_1232_);
lean_dec(v_i_1231_);
return v_target_1233_;
}
else
{
lean_object* v_es_1236_; lean_object* v___x_1237_; lean_object* v_source_1238_; lean_object* v_target_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_es_1236_ = lean_array_fget(v_source_1232_, v_i_1231_);
v___x_1237_ = lean_box(0);
v_source_1238_ = lean_array_fset(v_source_1232_, v_i_1231_, v___x_1237_);
v_target_1239_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_target_1233_, v_es_1236_);
v___x_1240_ = lean_unsigned_to_nat(1u);
v___x_1241_ = lean_nat_add(v_i_1231_, v___x_1240_);
lean_dec(v_i_1231_);
v_i_1231_ = v___x_1241_;
v_source_1232_ = v_source_1238_;
v_target_1233_ = v_target_1239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(lean_object* v_data_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_nbuckets_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1244_ = lean_array_get_size(v_data_1243_);
v___x_1245_ = lean_unsigned_to_nat(2u);
v_nbuckets_1246_ = lean_nat_mul(v___x_1244_, v___x_1245_);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = lean_box(0);
v___x_1249_ = lean_mk_array(v_nbuckets_1246_, v___x_1248_);
v___x_1250_ = lean_array_propagate_mark(v_data_1243_, v___x_1249_);
v___x_1251_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v___x_1247_, v_data_1243_, v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(lean_object* v_a_1252_, lean_object* v_b_1253_, lean_object* v_x_1254_){
_start:
{
if (lean_obj_tag(v_x_1254_) == 0)
{
lean_dec(v_b_1253_);
lean_dec_ref(v_a_1252_);
return v_x_1254_;
}
else
{
lean_object* v_key_1255_; lean_object* v_value_1256_; lean_object* v_tail_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1269_; 
v_key_1255_ = lean_ctor_get(v_x_1254_, 0);
v_value_1256_ = lean_ctor_get(v_x_1254_, 1);
v_tail_1257_ = lean_ctor_get(v_x_1254_, 2);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_x_1254_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1259_ = v_x_1254_;
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_tail_1257_);
lean_inc(v_value_1256_);
lean_inc(v_key_1255_);
lean_dec(v_x_1254_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
uint8_t v___x_1261_; 
v___x_1261_ = l_Lean_ExprStructEq_beq(v_key_1255_, v_a_1252_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1252_, v_b_1253_, v_tail_1257_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 2, v___x_1262_);
v___x_1264_ = v___x_1259_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_key_1255_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_value_1256_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
else
{
lean_object* v___x_1267_; 
lean_dec(v_value_1256_);
lean_dec(v_key_1255_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v_b_1253_);
lean_ctor_set(v___x_1259_, 0, v_a_1252_);
v___x_1267_ = v___x_1259_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1252_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_b_1253_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_tail_1257_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object* v_a_1270_, lean_object* v_x_1271_){
_start:
{
if (lean_obj_tag(v_x_1271_) == 0)
{
uint8_t v___x_1272_; 
v___x_1272_ = 0;
return v___x_1272_;
}
else
{
lean_object* v_key_1273_; lean_object* v_tail_1274_; uint8_t v___x_1275_; 
v_key_1273_ = lean_ctor_get(v_x_1271_, 0);
v_tail_1274_ = lean_ctor_get(v_x_1271_, 2);
v___x_1275_ = l_Lean_ExprStructEq_beq(v_key_1273_, v_a_1270_);
if (v___x_1275_ == 0)
{
v_x_1271_ = v_tail_1274_;
goto _start;
}
else
{
return v___x_1275_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1270_ = stack[0].m_obj;
lean_object* v_x_1271_ = stack[1].m_obj;
uint8_t v_res_1277_;
v_res_1277_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1270_, v_x_1271_);
stack->m_num = v_res_1277_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object* v_a_1278_, lean_object* v_x_1279_){
_start:
{
uint8_t v_res_1280_; lean_object* v_r_1281_; 
v_res_1280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1278_, v_x_1279_);
lean_dec(v_x_1279_);
lean_dec_ref(v_a_1278_);
v_r_1281_ = lean_box(v_res_1280_);
return v_r_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object* v_m_1282_, lean_object* v_a_1283_, lean_object* v_b_1284_){
_start:
{
lean_object* v_size_1285_; lean_object* v_buckets_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1329_; 
v_size_1285_ = lean_ctor_get(v_m_1282_, 0);
v_buckets_1286_ = lean_ctor_get(v_m_1282_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_m_1282_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1288_ = v_m_1282_;
v_isShared_1289_ = v_isSharedCheck_1329_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_buckets_1286_);
lean_inc(v_size_1285_);
lean_dec(v_m_1282_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1329_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; uint64_t v___x_1291_; uint64_t v___x_1292_; uint64_t v___x_1293_; uint64_t v_fold_1294_; uint64_t v___x_1295_; uint64_t v___x_1296_; uint64_t v___x_1297_; size_t v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; lean_object* v_bkt_1303_; uint8_t v___x_1304_; 
v___x_1290_ = lean_array_get_size(v_buckets_1286_);
v___x_1291_ = l_Lean_ExprStructEq_hash(v_a_1283_);
v___x_1292_ = 32ULL;
v___x_1293_ = lean_uint64_shift_right(v___x_1291_, v___x_1292_);
v_fold_1294_ = lean_uint64_xor(v___x_1291_, v___x_1293_);
v___x_1295_ = 16ULL;
v___x_1296_ = lean_uint64_shift_right(v_fold_1294_, v___x_1295_);
v___x_1297_ = lean_uint64_xor(v_fold_1294_, v___x_1296_);
v___x_1298_ = lean_uint64_to_usize(v___x_1297_);
v___x_1299_ = lean_usize_of_nat(v___x_1290_);
v___x_1300_ = ((size_t)1ULL);
v___x_1301_ = lean_usize_sub(v___x_1299_, v___x_1300_);
v___x_1302_ = lean_usize_land(v___x_1298_, v___x_1301_);
v_bkt_1303_ = lean_array_uget_borrowed(v_buckets_1286_, v___x_1302_);
v___x_1304_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1283_, v_bkt_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v_size_x27_1306_; lean_object* v___x_1307_; lean_object* v_buckets_x27_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1305_ = lean_unsigned_to_nat(1u);
v_size_x27_1306_ = lean_nat_add(v_size_1285_, v___x_1305_);
lean_dec(v_size_1285_);
lean_inc(v_bkt_1303_);
v___x_1307_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1307_, 0, v_a_1283_);
lean_ctor_set(v___x_1307_, 1, v_b_1284_);
lean_ctor_set(v___x_1307_, 2, v_bkt_1303_);
v_buckets_x27_1308_ = lean_array_uset(v_buckets_1286_, v___x_1302_, v___x_1307_);
v___x_1309_ = lean_unsigned_to_nat(4u);
v___x_1310_ = lean_nat_mul(v_size_x27_1306_, v___x_1309_);
v___x_1311_ = lean_unsigned_to_nat(3u);
v___x_1312_ = lean_nat_div(v___x_1310_, v___x_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_array_get_size(v_buckets_x27_1308_);
v___x_1314_ = lean_nat_dec_le(v___x_1312_, v___x_1313_);
lean_dec(v___x_1312_);
if (v___x_1314_ == 0)
{
lean_object* v_val_1315_; lean_object* v___x_1317_; 
v_val_1315_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_buckets_x27_1308_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v_val_1315_);
lean_ctor_set(v___x_1288_, 0, v_size_x27_1306_);
v___x_1317_ = v___x_1288_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_size_x27_1306_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_val_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
else
{
lean_object* v___x_1320_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v_buckets_x27_1308_);
lean_ctor_set(v___x_1288_, 0, v_size_x27_1306_);
v___x_1320_ = v___x_1288_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_size_x27_1306_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_buckets_x27_1308_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
else
{
lean_object* v___x_1322_; lean_object* v_buckets_x27_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
lean_inc(v_bkt_1303_);
v___x_1322_ = lean_box(0);
v_buckets_x27_1323_ = lean_array_uset(v_buckets_1286_, v___x_1302_, v___x_1322_);
v___x_1324_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1283_, v_b_1284_, v_bkt_1303_);
v___x_1325_ = lean_array_uset(v_buckets_x27_1323_, v___x_1302_, v___x_1324_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v___x_1325_);
v___x_1327_ = v___x_1288_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_size_1285_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1325_);
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
}
lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* v_e_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
switch(lean_obj_tag(v_e_1330_))
{
case 11:
{
lean_object* v_typeName_1338_; lean_object* v_idx_1339_; lean_object* v_struct_1340_; lean_object* v___x_1341_; 
v_typeName_1338_ = lean_ctor_get(v_e_1330_, 0);
v_idx_1339_ = lean_ctor_get(v_e_1330_, 1);
v_struct_1340_ = lean_ctor_get(v_e_1330_, 2);
lean_inc_ref(v_struct_1340_);
v___x_1341_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_struct_1340_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1356_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1356_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1356_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
size_t v___x_1346_; size_t v___x_1347_; uint8_t v___x_1348_; 
v___x_1346_ = lean_ptr_addr(v_struct_1340_);
v___x_1347_ = lean_ptr_addr(v_a_1342_);
v___x_1348_ = lean_usize_dec_eq(v___x_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
lean_inc(v_idx_1339_);
lean_inc(v_typeName_1338_);
lean_dec_ref_known(v_e_1330_, 3);
v___x_1349_ = l_Lean_Expr_proj___override(v_typeName_1338_, v_idx_1339_, v_a_1342_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1349_);
v___x_1351_ = v___x_1344_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
else
{
lean_object* v___x_1354_; 
lean_dec(v_a_1342_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v_e_1330_);
v___x_1354_ = v___x_1344_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_e_1330_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1330_, 3);
return v___x_1341_;
}
}
case 7:
{
lean_object* v_binderName_1357_; lean_object* v_binderType_1358_; lean_object* v_body_1359_; uint8_t v_binderInfo_1360_; lean_object* v___x_1361_; 
v_binderName_1357_ = lean_ctor_get(v_e_1330_, 0);
v_binderType_1358_ = lean_ctor_get(v_e_1330_, 1);
v_body_1359_ = lean_ctor_get(v_e_1330_, 2);
v_binderInfo_1360_ = lean_ctor_get_uint8(v_e_1330_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1358_);
v___x_1361_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1358_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1361_, 1);
lean_inc_ref(v_body_1359_);
v___x_1363_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1359_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1390_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1390_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1390_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
size_t v___x_1368_; size_t v___x_1369_; uint8_t v___x_1370_; 
v___x_1368_ = lean_ptr_addr(v_binderType_1358_);
v___x_1369_ = lean_ptr_addr(v_a_1362_);
v___x_1370_ = lean_usize_dec_eq(v___x_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
lean_inc(v_binderName_1357_);
lean_dec_ref_known(v_e_1330_, 3);
v___x_1371_ = l_Lean_Expr_forallE___override(v_binderName_1357_, v_a_1362_, v_a_1364_, v_binderInfo_1360_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1371_);
v___x_1373_ = v___x_1366_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
size_t v___x_1375_; size_t v___x_1376_; uint8_t v___x_1377_; 
v___x_1375_ = lean_ptr_addr(v_body_1359_);
v___x_1376_ = lean_ptr_addr(v_a_1364_);
v___x_1377_ = lean_usize_dec_eq(v___x_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_inc(v_binderName_1357_);
lean_dec_ref_known(v_e_1330_, 3);
v___x_1378_ = l_Lean_Expr_forallE___override(v_binderName_1357_, v_a_1362_, v_a_1364_, v_binderInfo_1360_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1378_);
v___x_1380_ = v___x_1366_;
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
uint8_t v___x_1382_; 
v___x_1382_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1360_, v_binderInfo_1360_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
lean_inc(v_binderName_1357_);
lean_dec_ref_known(v_e_1330_, 3);
v___x_1383_ = l_Lean_Expr_forallE___override(v_binderName_1357_, v_a_1362_, v_a_1364_, v_binderInfo_1360_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1383_);
v___x_1385_ = v___x_1366_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
else
{
lean_object* v___x_1388_; 
lean_dec(v_a_1364_);
lean_dec(v_a_1362_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v_e_1330_);
v___x_1388_ = v___x_1366_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_e_1330_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1362_);
lean_dec_ref_known(v_e_1330_, 3);
return v___x_1363_;
}
}
else
{
lean_dec_ref_known(v_e_1330_, 3);
return v___x_1361_;
}
}
case 6:
{
lean_object* v_binderName_1391_; lean_object* v_binderType_1392_; lean_object* v_body_1393_; uint8_t v_binderInfo_1394_; lean_object* v___x_1395_; 
v_binderName_1391_ = lean_ctor_get(v_e_1330_, 0);
v_binderType_1392_ = lean_ctor_get(v_e_1330_, 1);
v_body_1393_ = lean_ctor_get(v_e_1330_, 2);
v_binderInfo_1394_ = lean_ctor_get_uint8(v_e_1330_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1392_);
v___x_1395_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1392_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
lean_inc_ref(v_body_1393_);
v___x_1397_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1393_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1424_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1424_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1424_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
size_t v___x_1402_; size_t v___x_1403_; uint8_t v___x_1404_; 
v___x_1402_ = lean_ptr_addr(v_binderType_1392_);
v___x_1403_ = lean_ptr_addr(v_a_1396_);
v___x_1404_ = lean_usize_dec_eq(v___x_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_inc(v_binderName_1391_);
lean_dec_ref_known(v_e_1330_, 3);
v___x_1405_ = l_Lean_Expr_lam___override(v_binderName_1391_, v_a_1396_, v_a_1398_, v_binderInfo_1394_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1405_);
v___x_1407_ = v___x_1400_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
size_t v___x_1409_; size_t v___x_1410_; uint8_t v___x_1411_; 
v___x_1409_ = lean_ptr_addr(v_body_1393_);
v___x_1410_ = lean_ptr_addr(v_a_1398_);
v___x_1411_ = lean_usize_dec_eq(v___x_1409_, v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_inc(v_binderName_1391_);
lean_dec_ref_known(v_e_1330_, 3);
v___x_1412_ = l_Lean_Expr_lam___override(v_binderName_1391_, v_a_1396_, v_a_1398_, v_binderInfo_1394_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1412_);
v___x_1414_ = v___x_1400_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1394_, v_binderInfo_1394_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
lean_inc(v_binderName_1391_);
lean_dec_ref_known(v_e_1330_, 3);
v___x_1417_ = l_Lean_Expr_lam___override(v_binderName_1391_, v_a_1396_, v_a_1398_, v_binderInfo_1394_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1417_);
v___x_1419_ = v___x_1400_;
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
lean_object* v___x_1422_; 
lean_dec(v_a_1398_);
lean_dec(v_a_1396_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v_e_1330_);
v___x_1422_ = v___x_1400_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_e_1330_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1396_);
lean_dec_ref_known(v_e_1330_, 3);
return v___x_1397_;
}
}
else
{
lean_dec_ref_known(v_e_1330_, 3);
return v___x_1395_;
}
}
case 8:
{
lean_object* v_declName_1425_; lean_object* v_type_1426_; lean_object* v_value_1427_; lean_object* v_body_1428_; uint8_t v_nondep_1429_; lean_object* v___x_1430_; 
v_declName_1425_ = lean_ctor_get(v_e_1330_, 0);
v_type_1426_ = lean_ctor_get(v_e_1330_, 1);
v_value_1427_ = lean_ctor_get(v_e_1330_, 2);
v_body_1428_ = lean_ctor_get(v_e_1330_, 3);
v_nondep_1429_ = lean_ctor_get_uint8(v_e_1330_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1426_);
v___x_1430_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_type_1426_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
lean_inc_ref(v_value_1427_);
v___x_1432_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_value_1427_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1434_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
lean_inc_ref(v_body_1428_);
v___x_1434_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1428_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1463_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1463_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1463_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
size_t v___x_1439_; size_t v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = lean_ptr_addr(v_type_1426_);
v___x_1440_ = lean_ptr_addr(v_a_1431_);
v___x_1441_ = lean_usize_dec_eq(v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
lean_inc(v_declName_1425_);
lean_dec_ref_known(v_e_1330_, 4);
v___x_1442_ = l_Lean_Expr_letE___override(v_declName_1425_, v_a_1431_, v_a_1433_, v_a_1435_, v_nondep_1429_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1442_);
v___x_1444_ = v___x_1437_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
else
{
size_t v___x_1446_; size_t v___x_1447_; uint8_t v___x_1448_; 
v___x_1446_ = lean_ptr_addr(v_value_1427_);
v___x_1447_ = lean_ptr_addr(v_a_1433_);
v___x_1448_ = lean_usize_dec_eq(v___x_1446_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
lean_inc(v_declName_1425_);
lean_dec_ref_known(v_e_1330_, 4);
v___x_1449_ = l_Lean_Expr_letE___override(v_declName_1425_, v_a_1431_, v_a_1433_, v_a_1435_, v_nondep_1429_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1449_);
v___x_1451_ = v___x_1437_;
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
v___x_1453_ = lean_ptr_addr(v_body_1428_);
v___x_1454_ = lean_ptr_addr(v_a_1435_);
v___x_1455_ = lean_usize_dec_eq(v___x_1453_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_inc(v_declName_1425_);
lean_dec_ref_known(v_e_1330_, 4);
v___x_1456_ = l_Lean_Expr_letE___override(v_declName_1425_, v_a_1431_, v_a_1433_, v_a_1435_, v_nondep_1429_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1456_);
v___x_1458_ = v___x_1437_;
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
lean_dec(v_a_1435_);
lean_dec(v_a_1433_);
lean_dec(v_a_1431_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v_e_1330_);
v___x_1461_ = v___x_1437_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_e_1330_);
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
}
else
{
lean_dec(v_a_1433_);
lean_dec(v_a_1431_);
lean_dec_ref_known(v_e_1330_, 4);
return v___x_1434_;
}
}
else
{
lean_dec(v_a_1431_);
lean_dec_ref_known(v_e_1330_, 4);
return v___x_1432_;
}
}
else
{
lean_dec_ref_known(v_e_1330_, 4);
return v___x_1430_;
}
}
case 5:
{
lean_object* v_fn_1464_; lean_object* v_arg_1465_; lean_object* v___x_1466_; 
v_fn_1464_ = lean_ctor_get(v_e_1330_, 0);
v_arg_1465_ = lean_ctor_get(v_e_1330_, 1);
lean_inc_ref(v_fn_1464_);
v___x_1466_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_fn_1464_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
lean_inc_ref(v_arg_1465_);
v___x_1468_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_arg_1465_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1490_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1490_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1490_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
size_t v___x_1473_; size_t v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = lean_ptr_addr(v_fn_1464_);
v___x_1474_ = lean_ptr_addr(v_a_1467_);
v___x_1475_ = lean_usize_dec_eq(v___x_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
lean_dec_ref_known(v_e_1330_, 2);
v___x_1476_ = l_Lean_Expr_app___override(v_a_1467_, v_a_1469_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1476_);
v___x_1478_ = v___x_1471_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
else
{
size_t v___x_1480_; size_t v___x_1481_; uint8_t v___x_1482_; 
v___x_1480_ = lean_ptr_addr(v_arg_1465_);
v___x_1481_ = lean_ptr_addr(v_a_1469_);
v___x_1482_ = lean_usize_dec_eq(v___x_1480_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
lean_dec_ref_known(v_e_1330_, 2);
v___x_1483_ = l_Lean_Expr_app___override(v_a_1467_, v_a_1469_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1483_);
v___x_1485_ = v___x_1471_;
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
lean_dec(v_a_1469_);
lean_dec(v_a_1467_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v_e_1330_);
v___x_1488_ = v___x_1471_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_e_1330_);
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
}
else
{
lean_dec(v_a_1467_);
lean_dec_ref_known(v_e_1330_, 2);
return v___x_1468_;
}
}
else
{
lean_dec_ref_known(v_e_1330_, 2);
return v___x_1466_;
}
}
case 10:
{
lean_object* v_data_1491_; lean_object* v_expr_1492_; lean_object* v___x_1493_; 
v_data_1491_ = lean_ctor_get(v_e_1330_, 0);
v_expr_1492_ = lean_ctor_get(v_e_1330_, 1);
lean_inc_ref(v_expr_1492_);
v___x_1493_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_expr_1492_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
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
v___x_1498_ = lean_ptr_addr(v_expr_1492_);
v___x_1499_ = lean_ptr_addr(v_a_1494_);
v___x_1500_ = lean_usize_dec_eq(v___x_1498_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
lean_inc(v_data_1491_);
lean_dec_ref_known(v_e_1330_, 2);
v___x_1501_ = l_Lean_Expr_mdata___override(v_data_1491_, v_a_1494_);
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
lean_ctor_set(v___x_1496_, 0, v_e_1330_);
v___x_1506_ = v___x_1496_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_e_1330_);
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
lean_dec_ref_known(v_e_1330_, 2);
return v___x_1493_;
}
}
case 3:
{
lean_object* v_u_1509_; lean_object* v___x_1510_; 
v_u_1509_ = lean_ctor_get(v_e_1330_, 0);
lean_inc(v_u_1509_);
v___x_1510_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_1509_, v_a_1332_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1525_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1525_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1525_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
size_t v___x_1515_; size_t v___x_1516_; uint8_t v___x_1517_; 
v___x_1515_ = lean_ptr_addr(v_u_1509_);
v___x_1516_ = lean_ptr_addr(v_a_1511_);
v___x_1517_ = lean_usize_dec_eq(v___x_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
lean_dec_ref_known(v_e_1330_, 1);
v___x_1518_ = l_Lean_Expr_sort___override(v_a_1511_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1518_);
v___x_1520_ = v___x_1513_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
else
{
lean_object* v___x_1523_; 
lean_dec(v_a_1511_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v_e_1330_);
v___x_1523_ = v___x_1513_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_e_1330_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec_ref_known(v_e_1330_, 1);
v_a_1526_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1510_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1510_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
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
case 4:
{
lean_object* v_declName_1534_; lean_object* v_us_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_declName_1534_ = lean_ctor_get(v_e_1330_, 0);
v_us_1535_ = lean_ctor_get(v_e_1330_, 1);
v___x_1536_ = lean_box(0);
lean_inc(v_us_1535_);
v___x_1537_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_us_1535_, v___x_1536_, v_a_1332_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1550_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1550_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1550_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
uint8_t v___x_1542_; 
v___x_1542_ = l_ptrEqList___redArg(v_us_1535_, v_a_1538_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
lean_inc(v_declName_1534_);
lean_dec_ref_known(v_e_1330_, 2);
v___x_1543_ = l_Lean_Expr_const___override(v_declName_1534_, v_a_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1543_);
v___x_1545_ = v___x_1540_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
else
{
lean_object* v___x_1548_; 
lean_dec(v_a_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v_e_1330_);
v___x_1548_ = v___x_1540_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_e_1330_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref_known(v_e_1330_, 2);
v_a_1551_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1537_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1537_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_1559_; lean_object* v___f_1560_; lean_object* v___x_1561_; 
v_mvarId_1559_ = lean_ctor_get(v_e_1330_, 0);
lean_inc_ref(v_e_1330_);
v___f_1560_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1560_, 0, v_e_1330_);
lean_inc(v_mvarId_1559_);
v___x_1561_ = l_Lean_MVarId_getDecl(v_mvarId_1559_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v_type_1563_; lean_object* v___x_1564_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v_type_1563_ = lean_ctor_get(v_a_1562_, 2);
lean_inc_ref_n(v_type_1563_, 2);
lean_dec(v_a_1562_);
v___x_1564_ = l_Lean_Meta_Closure_preprocess(v_type_1563_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1566_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1565_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v___x_1568_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
v___x_1570_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_1332_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1632_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1632_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1632_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_e_x27_1576_; lean_object* v___y_1577_; lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_1559_, v_a_1334_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
if (lean_obj_tag(v_a_1610_) == 1)
{
lean_object* v_val_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref_known(v_e_1330_, 1);
v_val_1611_ = lean_ctor_get(v_a_1610_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_a_1610_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1613_ = v_a_1610_;
v_isShared_1614_ = v_isSharedCheck_1623_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_val_1611_);
lean_dec(v_a_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1623_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_fvars_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v_fvars_1615_ = lean_ctor_get(v_val_1611_, 0);
lean_inc_ref(v_fvars_1615_);
lean_dec(v_val_1611_);
v___x_1616_ = lean_array_get_size(v_fvars_1615_);
lean_dec_ref(v_fvars_1615_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1616_);
v___x_1618_ = v___x_1613_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
uint8_t v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = 0;
v___x_1620_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1563_, v___x_1618_, v___f_1560_, v___x_1619_, v___x_1619_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v_e_x27_1576_ = v_a_1621_;
v___y_1577_ = v_a_1332_;
goto v___jp_1575_;
}
else
{
lean_del_object(v___x_1573_);
lean_dec(v_a_1571_);
lean_dec(v_a_1569_);
lean_dec(v_a_1567_);
return v___x_1620_;
}
}
}
}
else
{
lean_dec(v_a_1610_);
lean_dec_ref(v_type_1563_);
lean_dec_ref(v___f_1560_);
v_e_x27_1576_ = v_e_1330_;
v___y_1577_ = v_a_1332_;
goto v___jp_1575_;
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_del_object(v___x_1573_);
lean_dec(v_a_1571_);
lean_dec(v_a_1569_);
lean_dec(v_a_1567_);
lean_dec_ref(v_type_1563_);
lean_dec_ref(v___f_1560_);
lean_dec_ref_known(v_e_1330_, 1);
v_a_1624_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1609_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1609_);
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
v___jp_1575_:
{
lean_object* v___x_1578_; lean_object* v_visitedLevel_1579_; lean_object* v_visitedExpr_1580_; lean_object* v_levelParams_1581_; lean_object* v_nextLevelIdx_1582_; lean_object* v_levelArgs_1583_; lean_object* v_newLocalDecls_1584_; lean_object* v_newLocalDeclsForMVars_1585_; lean_object* v_newLetDecls_1586_; lean_object* v_nextExprIdx_1587_; lean_object* v_exprMVarArgs_1588_; lean_object* v_exprFVarArgs_1589_; lean_object* v_toProcess_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1608_; 
v___x_1578_ = lean_st_ref_take(v___y_1577_);
v_visitedLevel_1579_ = lean_ctor_get(v___x_1578_, 0);
v_visitedExpr_1580_ = lean_ctor_get(v___x_1578_, 1);
v_levelParams_1581_ = lean_ctor_get(v___x_1578_, 2);
v_nextLevelIdx_1582_ = lean_ctor_get(v___x_1578_, 3);
v_levelArgs_1583_ = lean_ctor_get(v___x_1578_, 4);
v_newLocalDecls_1584_ = lean_ctor_get(v___x_1578_, 5);
v_newLocalDeclsForMVars_1585_ = lean_ctor_get(v___x_1578_, 6);
v_newLetDecls_1586_ = lean_ctor_get(v___x_1578_, 7);
v_nextExprIdx_1587_ = lean_ctor_get(v___x_1578_, 8);
v_exprMVarArgs_1588_ = lean_ctor_get(v___x_1578_, 9);
v_exprFVarArgs_1589_ = lean_ctor_get(v___x_1578_, 10);
v_toProcess_1590_ = lean_ctor_get(v___x_1578_, 11);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1592_ = v___x_1578_;
v_isShared_1593_ = v_isSharedCheck_1608_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_toProcess_1590_);
lean_inc(v_exprFVarArgs_1589_);
lean_inc(v_exprMVarArgs_1588_);
lean_inc(v_nextExprIdx_1587_);
lean_inc(v_newLetDecls_1586_);
lean_inc(v_newLocalDeclsForMVars_1585_);
lean_inc(v_newLocalDecls_1584_);
lean_inc(v_levelArgs_1583_);
lean_inc(v_nextLevelIdx_1582_);
lean_inc(v_levelParams_1581_);
lean_inc(v_visitedExpr_1580_);
lean_inc(v_visitedLevel_1579_);
lean_dec(v___x_1578_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1608_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; uint8_t v___x_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = 0;
v___x_1596_ = 0;
lean_inc(v_a_1569_);
v___x_1597_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1597_, 0, v___x_1594_);
lean_ctor_set(v___x_1597_, 1, v_a_1569_);
lean_ctor_set(v___x_1597_, 2, v_a_1571_);
lean_ctor_set(v___x_1597_, 3, v_a_1567_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*4, v___x_1595_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*4 + 1, v___x_1596_);
v___x_1598_ = lean_array_push(v_newLocalDeclsForMVars_1585_, v___x_1597_);
v___x_1599_ = lean_array_push(v_exprMVarArgs_1588_, v_e_x27_1576_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 9, v___x_1599_);
lean_ctor_set(v___x_1592_, 6, v___x_1598_);
v___x_1601_ = v___x_1592_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_visitedLevel_1579_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_visitedExpr_1580_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_levelParams_1581_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_nextLevelIdx_1582_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_levelArgs_1583_);
lean_ctor_set(v_reuseFailAlloc_1607_, 5, v_newLocalDecls_1584_);
lean_ctor_set(v_reuseFailAlloc_1607_, 6, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1607_, 7, v_newLetDecls_1586_);
lean_ctor_set(v_reuseFailAlloc_1607_, 8, v_nextExprIdx_1587_);
lean_ctor_set(v_reuseFailAlloc_1607_, 9, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1607_, 10, v_exprFVarArgs_1589_);
lean_ctor_set(v_reuseFailAlloc_1607_, 11, v_toProcess_1590_);
v___x_1601_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1602_ = lean_st_ref_put(v___y_1577_, v___x_1601_);
v___x_1603_ = l_Lean_mkFVar(v_a_1569_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1603_);
v___x_1605_ = v___x_1573_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_a_1569_);
lean_dec(v_a_1567_);
lean_dec_ref(v_type_1563_);
lean_dec_ref(v___f_1560_);
lean_dec_ref_known(v_e_1330_, 1);
v_a_1633_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1570_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1570_);
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
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_a_1567_);
lean_dec_ref(v_type_1563_);
lean_dec_ref(v___f_1560_);
lean_dec_ref_known(v_e_1330_, 1);
v_a_1641_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1568_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1568_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
else
{
lean_dec_ref(v_type_1563_);
lean_dec_ref(v___f_1560_);
lean_dec_ref_known(v_e_1330_, 1);
return v___x_1566_;
}
}
else
{
lean_dec_ref(v_type_1563_);
lean_dec_ref(v___f_1560_);
lean_dec_ref_known(v_e_1330_, 1);
return v___x_1564_;
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec_ref(v___f_1560_);
lean_dec_ref_known(v_e_1330_, 1);
v_a_1649_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1561_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1561_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_1657_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; uint8_t v___x_1694_; lean_object* v___x_1695_; 
v_fvarId_1657_ = lean_ctor_get(v_e_1330_, 0);
lean_inc_n(v_fvarId_1657_, 2);
lean_dec_ref_known(v_e_1330_, 1);
v___x_1694_ = 0;
v___x_1695_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_1657_, v___x_1694_, v_a_1333_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1695_) == 0)
{
uint8_t v_zetaDelta_1696_; 
v_zetaDelta_1696_ = lean_ctor_get_uint8(v_a_1331_, 0);
if (v_zetaDelta_1696_ == 1)
{
lean_object* v_a_1697_; 
v_a_1697_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1695_, 1);
if (lean_obj_tag(v_a_1697_) == 1)
{
lean_object* v_val_1698_; lean_object* v___x_1699_; 
lean_dec(v_fvarId_1657_);
v_val_1698_ = lean_ctor_get(v_a_1697_, 0);
lean_inc(v_val_1698_);
lean_dec_ref_known(v_a_1697_, 1);
v___x_1699_ = l_Lean_Meta_Closure_preprocess(v_val_1698_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1701_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1699_, 1);
v___x_1701_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1700_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
return v___x_1701_;
}
else
{
return v___x_1699_;
}
}
else
{
lean_dec(v_a_1697_);
v___y_1659_ = v_a_1331_;
v___y_1660_ = v_a_1332_;
v___y_1661_ = v_a_1333_;
v___y_1662_ = v_a_1334_;
v___y_1663_ = v_a_1335_;
v___y_1664_ = v_a_1336_;
goto v___jp_1658_;
}
}
else
{
lean_dec_ref_known(v___x_1695_, 1);
v___y_1659_ = v_a_1331_;
v___y_1660_ = v_a_1332_;
v___y_1661_ = v_a_1333_;
v___y_1662_ = v_a_1334_;
v___y_1663_ = v_a_1335_;
v___y_1664_ = v_a_1336_;
goto v___jp_1658_;
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_fvarId_1657_);
v_a_1702_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1695_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1695_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
v___jp_1658_:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc_n(v_a_1666_, 2);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_fvarId_1657_);
lean_ctor_set(v___x_1667_, 1, v_a_1666_);
v___x_1668_ = l_Lean_Meta_Closure_pushToProcess___redArg(v___x_1667_, v___y_1660_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1676_; 
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v___x_1668_, 0);
lean_dec(v_unused_1677_);
v___x_1670_ = v___x_1668_;
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
else
{
lean_dec(v___x_1668_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1672_ = l_Lean_mkFVar(v_a_1666_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1672_);
v___x_1674_ = v___x_1670_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_a_1666_);
v_a_1678_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1668_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1668_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_fvarId_1657_);
v_a_1686_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1665_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1665_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
default: 
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_e_1330_);
return v___x_1710_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_collectExprAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1330_ = stack[0].m_obj;
lean_object* v_a_1331_ = stack[1].m_obj;
lean_object* v_a_1332_ = stack[2].m_obj;
lean_object* v_a_1333_ = stack[3].m_obj;
lean_object* v_a_1334_ = stack[4].m_obj;
lean_object* v_a_1335_ = stack[5].m_obj;
lean_object* v_a_1336_ = stack[6].m_obj;
lean_object* v_res_1711_;
v_res_1711_ = l_Lean_Meta_Closure_collectExprAux(v_e_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
stack->m_obj
 = v_res_1711_;
}
lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object* v_e_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
uint8_t v___x_1763_; 
v___x_1763_ = l_Lean_Expr_hasLevelParam(v_e_1712_);
if (v___x_1763_ == 0)
{
uint8_t v___x_1764_; 
v___x_1764_ = l_Lean_Expr_hasFVar(v_e_1712_);
if (v___x_1764_ == 0)
{
uint8_t v___x_1765_; 
v___x_1765_ = l_Lean_Expr_hasMVar(v_e_1712_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v_e_1712_);
return v___x_1766_;
}
else
{
goto v___jp_1720_;
}
}
else
{
goto v___jp_1720_;
}
}
else
{
goto v___jp_1720_;
}
v___jp_1720_:
{
lean_object* v___x_1721_; lean_object* v_visitedExpr_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_st_ref_get(v___y_1714_);
v_visitedExpr_1722_ = lean_ctor_get(v___x_1721_, 1);
lean_inc_ref(v_visitedExpr_1722_);
lean_dec(v___x_1721_);
v___x_1723_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1722_, v_e_1712_);
lean_dec_ref(v_visitedExpr_1722_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v___x_1724_; 
lean_inc_ref(v_e_1712_);
v___x_1724_ = l_Lean_Meta_Closure_collectExprAux(v_e_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1754_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1754_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1754_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v_visitedLevel_1730_; lean_object* v_visitedExpr_1731_; lean_object* v_levelParams_1732_; lean_object* v_nextLevelIdx_1733_; lean_object* v_levelArgs_1734_; lean_object* v_newLocalDecls_1735_; lean_object* v_newLocalDeclsForMVars_1736_; lean_object* v_newLetDecls_1737_; lean_object* v_nextExprIdx_1738_; lean_object* v_exprMVarArgs_1739_; lean_object* v_exprFVarArgs_1740_; lean_object* v_toProcess_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1753_; 
v___x_1729_ = lean_st_ref_take(v___y_1714_);
v_visitedLevel_1730_ = lean_ctor_get(v___x_1729_, 0);
v_visitedExpr_1731_ = lean_ctor_get(v___x_1729_, 1);
v_levelParams_1732_ = lean_ctor_get(v___x_1729_, 2);
v_nextLevelIdx_1733_ = lean_ctor_get(v___x_1729_, 3);
v_levelArgs_1734_ = lean_ctor_get(v___x_1729_, 4);
v_newLocalDecls_1735_ = lean_ctor_get(v___x_1729_, 5);
v_newLocalDeclsForMVars_1736_ = lean_ctor_get(v___x_1729_, 6);
v_newLetDecls_1737_ = lean_ctor_get(v___x_1729_, 7);
v_nextExprIdx_1738_ = lean_ctor_get(v___x_1729_, 8);
v_exprMVarArgs_1739_ = lean_ctor_get(v___x_1729_, 9);
v_exprFVarArgs_1740_ = lean_ctor_get(v___x_1729_, 10);
v_toProcess_1741_ = lean_ctor_get(v___x_1729_, 11);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1743_ = v___x_1729_;
v_isShared_1744_ = v_isSharedCheck_1753_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_toProcess_1741_);
lean_inc(v_exprFVarArgs_1740_);
lean_inc(v_exprMVarArgs_1739_);
lean_inc(v_nextExprIdx_1738_);
lean_inc(v_newLetDecls_1737_);
lean_inc(v_newLocalDeclsForMVars_1736_);
lean_inc(v_newLocalDecls_1735_);
lean_inc(v_levelArgs_1734_);
lean_inc(v_nextLevelIdx_1733_);
lean_inc(v_levelParams_1732_);
lean_inc(v_visitedExpr_1731_);
lean_inc(v_visitedLevel_1730_);
lean_dec(v___x_1729_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1753_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
lean_inc(v_a_1725_);
v___x_1745_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1731_, v_e_1712_, v_a_1725_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 1, v___x_1745_);
v___x_1747_ = v___x_1743_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_visitedLevel_1730_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v___x_1745_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_levelParams_1732_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_nextLevelIdx_1733_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v_levelArgs_1734_);
lean_ctor_set(v_reuseFailAlloc_1752_, 5, v_newLocalDecls_1735_);
lean_ctor_set(v_reuseFailAlloc_1752_, 6, v_newLocalDeclsForMVars_1736_);
lean_ctor_set(v_reuseFailAlloc_1752_, 7, v_newLetDecls_1737_);
lean_ctor_set(v_reuseFailAlloc_1752_, 8, v_nextExprIdx_1738_);
lean_ctor_set(v_reuseFailAlloc_1752_, 9, v_exprMVarArgs_1739_);
lean_ctor_set(v_reuseFailAlloc_1752_, 10, v_exprFVarArgs_1740_);
lean_ctor_set(v_reuseFailAlloc_1752_, 11, v_toProcess_1741_);
v___x_1747_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = lean_st_ref_put(v___y_1714_, v___x_1747_);
if (v_isShared_1728_ == 0)
{
v___x_1750_ = v___x_1727_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1725_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1712_);
return v___x_1724_;
}
}
else
{
lean_object* v_val_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref(v_e_1712_);
v_val_1755_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1723_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_val_1755_);
lean_dec(v___x_1723_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set_tag(v___x_1757_, 0);
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_val_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_collectExprAux___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1712_ = stack[0].m_obj;
lean_object* v___y_1713_ = stack[1].m_obj;
lean_object* v___y_1714_ = stack[2].m_obj;
lean_object* v___y_1715_ = stack[3].m_obj;
lean_object* v___y_1716_ = stack[4].m_obj;
lean_object* v___y_1717_ = stack[5].m_obj;
lean_object* v___y_1718_ = stack[6].m_obj;
lean_object* v_res_1767_;
v_res_1767_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_e_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
stack->m_obj
 = v_res_1767_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object* v_e_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_e_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* v_e_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_Meta_Closure_collectExprAux(v_e_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object* v_00_u03b2_1786_, lean_object* v_m_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1787_, v_a_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object* v_00_u03b2_1790_, lean_object* v_m_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(v_00_u03b2_1790_, v_m_1791_, v_a_1792_);
lean_dec_ref(v_a_1792_);
lean_dec_ref(v_m_1791_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object* v_00_u03b2_1794_, lean_object* v_m_1795_, lean_object* v_a_1796_, lean_object* v_b_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_1795_, v_a_1796_, v_b_1797_);
return v___x_1798_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object* v_x_1799_, lean_object* v_x_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1799_, v_x_1800_, v___y_1802_);
return v___x_1808_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1799_ = stack[0].m_obj;
lean_object* v_x_1800_ = stack[1].m_obj;
lean_object* v___y_1801_ = stack[2].m_obj;
lean_object* v___y_1802_ = stack[3].m_obj;
lean_object* v___y_1803_ = stack[4].m_obj;
lean_object* v___y_1804_ = stack[5].m_obj;
lean_object* v___y_1805_ = stack[6].m_obj;
lean_object* v___y_1806_ = stack[7].m_obj;
lean_object* v_res_1809_;
v_res_1809_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(v_x_1799_, v_x_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
stack->m_obj
 = v_res_1809_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object* v_x_1810_, lean_object* v_x_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(v_x_1810_, v_x_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
return v_res_1819_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1820_ = stack[0].m_obj;
lean_object* v___y_1821_ = stack[1].m_obj;
lean_object* v___y_1822_ = stack[2].m_obj;
lean_object* v___y_1823_ = stack[3].m_obj;
lean_object* v___y_1824_ = stack[4].m_obj;
lean_object* v___y_1825_ = stack[5].m_obj;
lean_object* v_res_1828_;
v_res_1828_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
stack->m_obj
 = v_res_1828_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___boxed(lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object* v_00_u03b2_1837_, lean_object* v_a_1838_, lean_object* v_x_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1838_, v_x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1841_, lean_object* v_a_1842_, lean_object* v_x_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(v_00_u03b2_1841_, v_a_1842_, v_x_1843_);
lean_dec(v_x_1843_);
lean_dec_ref(v_a_1842_);
return v_res_1844_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object* v_00_u03b2_1845_, lean_object* v_a_1846_, lean_object* v_x_1847_){
_start:
{
uint8_t v___x_1848_; 
v___x_1848_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1846_, v_x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1846_ = stack[1].m_obj;
lean_object* v_x_1847_ = stack[2].m_obj;
uint8_t v_res_1849_;
v_res_1849_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_box(0), v_a_1846_, v_x_1847_);
stack->m_num = v_res_1849_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1850_, lean_object* v_a_1851_, lean_object* v_x_1852_){
_start:
{
uint8_t v_res_1853_; lean_object* v_r_1854_; 
v_res_1853_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(v_00_u03b2_1850_, v_a_1851_, v_x_1852_);
lean_dec(v_x_1852_);
lean_dec_ref(v_a_1851_);
v_r_1854_ = lean_box(v_res_1853_);
return v_r_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3(lean_object* v_00_u03b2_1855_, lean_object* v_data_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_data_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4(lean_object* v_00_u03b2_1858_, lean_object* v_a_1859_, lean_object* v_b_1860_, lean_object* v_x_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1859_, v_b_1860_, v_x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1863_, lean_object* v_i_1864_, lean_object* v_source_1865_, lean_object* v_target_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v_i_1864_, v_source_1865_, v_target_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1868_, lean_object* v_x_1869_, lean_object* v_x_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_x_1869_, v_x_1870_);
return v___x_1871_;
}
}
lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* v_e_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_Meta_Closure_preprocess(v_e_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; uint8_t v___x_1925_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v___x_1925_ = l_Lean_Expr_hasLevelParam(v_a_1881_);
if (v___x_1925_ == 0)
{
uint8_t v___x_1926_; 
v___x_1926_ = l_Lean_Expr_hasFVar(v_a_1881_);
if (v___x_1926_ == 0)
{
uint8_t v___x_1927_; 
v___x_1927_ = l_Lean_Expr_hasMVar(v_a_1881_);
if (v___x_1927_ == 0)
{
return v___x_1880_;
}
else
{
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
goto v___jp_1882_;
}
}
else
{
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
goto v___jp_1882_;
}
}
else
{
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
goto v___jp_1882_;
}
v___jp_1882_:
{
lean_object* v___x_1883_; lean_object* v_visitedExpr_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_st_ref_get(v_a_1874_);
v_visitedExpr_1884_ = lean_ctor_get(v___x_1883_, 1);
lean_inc_ref(v_visitedExpr_1884_);
lean_dec(v___x_1883_);
v___x_1885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1884_, v_a_1881_);
lean_dec_ref(v_visitedExpr_1884_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v___x_1886_; 
lean_inc(v_a_1881_);
v___x_1886_ = l_Lean_Meta_Closure_collectExprAux(v_a_1881_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1916_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1916_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1916_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v_visitedLevel_1892_; lean_object* v_visitedExpr_1893_; lean_object* v_levelParams_1894_; lean_object* v_nextLevelIdx_1895_; lean_object* v_levelArgs_1896_; lean_object* v_newLocalDecls_1897_; lean_object* v_newLocalDeclsForMVars_1898_; lean_object* v_newLetDecls_1899_; lean_object* v_nextExprIdx_1900_; lean_object* v_exprMVarArgs_1901_; lean_object* v_exprFVarArgs_1902_; lean_object* v_toProcess_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1915_; 
v___x_1891_ = lean_st_ref_take(v_a_1874_);
v_visitedLevel_1892_ = lean_ctor_get(v___x_1891_, 0);
v_visitedExpr_1893_ = lean_ctor_get(v___x_1891_, 1);
v_levelParams_1894_ = lean_ctor_get(v___x_1891_, 2);
v_nextLevelIdx_1895_ = lean_ctor_get(v___x_1891_, 3);
v_levelArgs_1896_ = lean_ctor_get(v___x_1891_, 4);
v_newLocalDecls_1897_ = lean_ctor_get(v___x_1891_, 5);
v_newLocalDeclsForMVars_1898_ = lean_ctor_get(v___x_1891_, 6);
v_newLetDecls_1899_ = lean_ctor_get(v___x_1891_, 7);
v_nextExprIdx_1900_ = lean_ctor_get(v___x_1891_, 8);
v_exprMVarArgs_1901_ = lean_ctor_get(v___x_1891_, 9);
v_exprFVarArgs_1902_ = lean_ctor_get(v___x_1891_, 10);
v_toProcess_1903_ = lean_ctor_get(v___x_1891_, 11);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1905_ = v___x_1891_;
v_isShared_1906_ = v_isSharedCheck_1915_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_toProcess_1903_);
lean_inc(v_exprFVarArgs_1902_);
lean_inc(v_exprMVarArgs_1901_);
lean_inc(v_nextExprIdx_1900_);
lean_inc(v_newLetDecls_1899_);
lean_inc(v_newLocalDeclsForMVars_1898_);
lean_inc(v_newLocalDecls_1897_);
lean_inc(v_levelArgs_1896_);
lean_inc(v_nextLevelIdx_1895_);
lean_inc(v_levelParams_1894_);
lean_inc(v_visitedExpr_1893_);
lean_inc(v_visitedLevel_1892_);
lean_dec(v___x_1891_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1915_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
lean_inc(v_a_1887_);
v___x_1907_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1893_, v_a_1881_, v_a_1887_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 1, v___x_1907_);
v___x_1909_ = v___x_1905_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_visitedLevel_1892_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_levelParams_1894_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_nextLevelIdx_1895_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_levelArgs_1896_);
lean_ctor_set(v_reuseFailAlloc_1914_, 5, v_newLocalDecls_1897_);
lean_ctor_set(v_reuseFailAlloc_1914_, 6, v_newLocalDeclsForMVars_1898_);
lean_ctor_set(v_reuseFailAlloc_1914_, 7, v_newLetDecls_1899_);
lean_ctor_set(v_reuseFailAlloc_1914_, 8, v_nextExprIdx_1900_);
lean_ctor_set(v_reuseFailAlloc_1914_, 9, v_exprMVarArgs_1901_);
lean_ctor_set(v_reuseFailAlloc_1914_, 10, v_exprFVarArgs_1902_);
lean_ctor_set(v_reuseFailAlloc_1914_, 11, v_toProcess_1903_);
v___x_1909_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1910_ = lean_st_ref_put(v_a_1874_, v___x_1909_);
if (v_isShared_1890_ == 0)
{
v___x_1912_ = v___x_1889_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1887_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
else
{
lean_dec(v_a_1881_);
return v___x_1886_;
}
}
else
{
lean_object* v_val_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_a_1881_);
v_val_1917_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1885_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_val_1917_);
lean_dec(v___x_1885_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set_tag(v___x_1919_, 0);
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_val_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
else
{
return v___x_1880_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_collectExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1872_ = stack[0].m_obj;
lean_object* v_a_1873_ = stack[1].m_obj;
lean_object* v_a_1874_ = stack[2].m_obj;
lean_object* v_a_1875_ = stack[3].m_obj;
lean_object* v_a_1876_ = stack[4].m_obj;
lean_object* v_a_1877_ = stack[5].m_obj;
lean_object* v_a_1878_ = stack[6].m_obj;
lean_object* v_res_1928_;
v_res_1928_ = l_Lean_Meta_Closure_collectExpr(v_e_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
stack->m_obj
 = v_res_1928_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* v_e_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_Meta_Closure_collectExpr(v_e_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* v_lctx_1938_, lean_object* v_i_1939_, lean_object* v_toProcess_1940_, lean_object* v_elem_1941_){
_start:
{
lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = lean_array_get_size(v_toProcess_1940_);
v___x_1943_ = lean_nat_dec_lt(v_i_1939_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_dec(v_i_1939_);
lean_dec_ref(v_lctx_1938_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v_elem_1941_);
lean_ctor_set(v___x_1944_, 1, v_toProcess_1940_);
return v___x_1944_;
}
else
{
lean_object* v_fvarId_1945_; lean_object* v_elem_x27_1946_; lean_object* v_fvarId_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v_fvarId_1945_ = lean_ctor_get(v_elem_1941_, 0);
v_elem_x27_1946_ = lean_array_fget_borrowed(v_toProcess_1940_, v_i_1939_);
v_fvarId_1947_ = lean_ctor_get(v_elem_x27_1946_, 0);
lean_inc(v_fvarId_1945_);
lean_inc_ref_n(v_lctx_1938_, 2);
v___x_1948_ = l_Lean_LocalContext_get_x21(v_lctx_1938_, v_fvarId_1945_);
v___x_1949_ = l_Lean_LocalDecl_index(v___x_1948_);
lean_dec_ref(v___x_1948_);
lean_inc(v_fvarId_1947_);
v___x_1950_ = l_Lean_LocalContext_get_x21(v_lctx_1938_, v_fvarId_1947_);
v___x_1951_ = l_Lean_LocalDecl_index(v___x_1950_);
lean_dec_ref(v___x_1950_);
v___x_1952_ = lean_nat_dec_lt(v___x_1949_, v___x_1951_);
lean_dec(v___x_1951_);
lean_dec(v___x_1949_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_unsigned_to_nat(1u);
v___x_1954_ = lean_nat_add(v_i_1939_, v___x_1953_);
lean_dec(v_i_1939_);
v_i_1939_ = v___x_1954_;
goto _start;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_inc(v_elem_x27_1946_);
v___x_1956_ = lean_unsigned_to_nat(1u);
v___x_1957_ = lean_nat_add(v_i_1939_, v___x_1956_);
v___x_1958_ = lean_array_fset(v_toProcess_1940_, v_i_1939_, v_elem_1941_);
lean_dec(v_i_1939_);
v_i_1939_ = v___x_1957_;
v_toProcess_1940_ = v___x_1958_;
v_elem_1941_ = v_elem_x27_1946_;
goto _start;
}
}
}
}
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v_lctx_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v_toProcess_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v_lctx_1963_ = lean_ctor_get(v_a_1961_, 2);
v___x_1964_ = ((lean_object*)(l_Lean_Meta_Closure_instInhabitedToProcessElement_default));
v___x_1965_ = lean_st_ref_get(v_a_1960_);
v_toProcess_1966_ = lean_ctor_get(v___x_1965_, 11);
lean_inc_ref(v_toProcess_1966_);
lean_dec(v___x_1965_);
v___x_1967_ = lean_array_get_size(v_toProcess_1966_);
lean_dec_ref(v_toProcess_1966_);
v___x_1968_ = lean_unsigned_to_nat(0u);
v___x_1969_ = lean_nat_dec_eq(v___x_1967_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v_visitedLevel_1971_; lean_object* v_visitedExpr_1972_; lean_object* v_levelParams_1973_; lean_object* v_nextLevelIdx_1974_; lean_object* v_levelArgs_1975_; lean_object* v_newLocalDecls_1976_; lean_object* v_newLocalDeclsForMVars_1977_; lean_object* v_newLetDecls_1978_; lean_object* v_nextExprIdx_1979_; lean_object* v_exprMVarArgs_1980_; lean_object* v_exprFVarArgs_1981_; lean_object* v_toProcess_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2000_; 
v___x_1970_ = lean_st_ref_take(v_a_1960_);
v_visitedLevel_1971_ = lean_ctor_get(v___x_1970_, 0);
v_visitedExpr_1972_ = lean_ctor_get(v___x_1970_, 1);
v_levelParams_1973_ = lean_ctor_get(v___x_1970_, 2);
v_nextLevelIdx_1974_ = lean_ctor_get(v___x_1970_, 3);
v_levelArgs_1975_ = lean_ctor_get(v___x_1970_, 4);
v_newLocalDecls_1976_ = lean_ctor_get(v___x_1970_, 5);
v_newLocalDeclsForMVars_1977_ = lean_ctor_get(v___x_1970_, 6);
v_newLetDecls_1978_ = lean_ctor_get(v___x_1970_, 7);
v_nextExprIdx_1979_ = lean_ctor_get(v___x_1970_, 8);
v_exprMVarArgs_1980_ = lean_ctor_get(v___x_1970_, 9);
v_exprFVarArgs_1981_ = lean_ctor_get(v___x_1970_, 10);
v_toProcess_1982_ = lean_ctor_get(v___x_1970_, 11);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1984_ = v___x_1970_;
v_isShared_1985_ = v_isSharedCheck_2000_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_toProcess_1982_);
lean_inc(v_exprFVarArgs_1981_);
lean_inc(v_exprMVarArgs_1980_);
lean_inc(v_nextExprIdx_1979_);
lean_inc(v_newLetDecls_1978_);
lean_inc(v_newLocalDeclsForMVars_1977_);
lean_inc(v_newLocalDecls_1976_);
lean_inc(v_levelArgs_1975_);
lean_inc(v_nextLevelIdx_1974_);
lean_inc(v_levelParams_1973_);
lean_inc(v_visitedExpr_1972_);
lean_inc(v_visitedLevel_1971_);
lean_dec(v___x_1970_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2000_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v_fst_1992_; lean_object* v_snd_1993_; lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1986_ = lean_array_get_size(v_toProcess_1982_);
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = lean_nat_sub(v___x_1986_, v___x_1987_);
v___x_1989_ = lean_array_get(v___x_1964_, v_toProcess_1982_, v___x_1988_);
lean_dec(v___x_1988_);
v___x_1990_ = lean_array_pop(v_toProcess_1982_);
lean_inc_ref(v_lctx_1963_);
v___x_1991_ = l_Lean_Meta_Closure_pickNextToProcessAux(v_lctx_1963_, v___x_1968_, v___x_1990_, v___x_1989_);
v_fst_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_fst_1992_);
v_snd_1993_ = lean_ctor_get(v___x_1991_, 1);
lean_inc(v_snd_1993_);
lean_dec_ref(v___x_1991_);
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_fst_1992_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 11, v_snd_1993_);
v___x_1996_ = v___x_1984_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_visitedLevel_1971_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_visitedExpr_1972_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_levelParams_1973_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v_nextLevelIdx_1974_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v_levelArgs_1975_);
lean_ctor_set(v_reuseFailAlloc_1999_, 5, v_newLocalDecls_1976_);
lean_ctor_set(v_reuseFailAlloc_1999_, 6, v_newLocalDeclsForMVars_1977_);
lean_ctor_set(v_reuseFailAlloc_1999_, 7, v_newLetDecls_1978_);
lean_ctor_set(v_reuseFailAlloc_1999_, 8, v_nextExprIdx_1979_);
lean_ctor_set(v_reuseFailAlloc_1999_, 9, v_exprMVarArgs_1980_);
lean_ctor_set(v_reuseFailAlloc_1999_, 10, v_exprFVarArgs_1981_);
lean_ctor_set(v_reuseFailAlloc_1999_, 11, v_snd_1993_);
v___x_1996_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_st_ref_put(v_a_1960_, v___x_1996_);
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1994_);
return v___x_1998_;
}
}
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_box(0);
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
return v___x_2002_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1960_ = stack[0].m_obj;
lean_object* v_a_1961_ = stack[1].m_obj;
lean_object* v_res_2003_;
v_res_2003_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1960_, v_a_1961_);
stack->m_obj
 = v_res_2003_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2004_, v_a_2005_);
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2004_);
return v_res_2007_;
}
}
lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2009_, v_a_2010_);
return v___x_2015_;
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_pickNextToProcess_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2008_ = stack[0].m_obj;
lean_object* v_a_2009_ = stack[1].m_obj;
lean_object* v_a_2010_ = stack[2].m_obj;
lean_object* v_a_2011_ = stack[3].m_obj;
lean_object* v_a_2012_ = stack[4].m_obj;
lean_object* v_a_2013_ = stack[5].m_obj;
lean_object* v_res_2016_;
v_res_2016_ = l_Lean_Meta_Closure_pickNextToProcess_x3f(v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
stack->m_obj
 = v_res_2016_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Lean_Meta_Closure_pickNextToProcess_x3f(v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
return v_res_2024_;
}
}
lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object* v_e_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v___x_2028_; lean_object* v_visitedLevel_2029_; lean_object* v_visitedExpr_2030_; lean_object* v_levelParams_2031_; lean_object* v_nextLevelIdx_2032_; lean_object* v_levelArgs_2033_; lean_object* v_newLocalDecls_2034_; lean_object* v_newLocalDeclsForMVars_2035_; lean_object* v_newLetDecls_2036_; lean_object* v_nextExprIdx_2037_; lean_object* v_exprMVarArgs_2038_; lean_object* v_exprFVarArgs_2039_; lean_object* v_toProcess_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2051_; 
v___x_2028_ = lean_st_ref_take(v_a_2026_);
v_visitedLevel_2029_ = lean_ctor_get(v___x_2028_, 0);
v_visitedExpr_2030_ = lean_ctor_get(v___x_2028_, 1);
v_levelParams_2031_ = lean_ctor_get(v___x_2028_, 2);
v_nextLevelIdx_2032_ = lean_ctor_get(v___x_2028_, 3);
v_levelArgs_2033_ = lean_ctor_get(v___x_2028_, 4);
v_newLocalDecls_2034_ = lean_ctor_get(v___x_2028_, 5);
v_newLocalDeclsForMVars_2035_ = lean_ctor_get(v___x_2028_, 6);
v_newLetDecls_2036_ = lean_ctor_get(v___x_2028_, 7);
v_nextExprIdx_2037_ = lean_ctor_get(v___x_2028_, 8);
v_exprMVarArgs_2038_ = lean_ctor_get(v___x_2028_, 9);
v_exprFVarArgs_2039_ = lean_ctor_get(v___x_2028_, 10);
v_toProcess_2040_ = lean_ctor_get(v___x_2028_, 11);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2042_ = v___x_2028_;
v_isShared_2043_ = v_isSharedCheck_2051_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_toProcess_2040_);
lean_inc(v_exprFVarArgs_2039_);
lean_inc(v_exprMVarArgs_2038_);
lean_inc(v_nextExprIdx_2037_);
lean_inc(v_newLetDecls_2036_);
lean_inc(v_newLocalDeclsForMVars_2035_);
lean_inc(v_newLocalDecls_2034_);
lean_inc(v_levelArgs_2033_);
lean_inc(v_nextLevelIdx_2032_);
lean_inc(v_levelParams_2031_);
lean_inc(v_visitedExpr_2030_);
lean_inc(v_visitedLevel_2029_);
lean_dec(v___x_2028_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2051_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_array_push(v_exprFVarArgs_2039_, v_e_2025_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 10, v___x_2045_);
v___x_2047_ = v___x_2042_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_visitedLevel_2029_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_visitedExpr_2030_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_levelParams_2031_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_nextLevelIdx_2032_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v_levelArgs_2033_);
lean_ctor_set(v_reuseFailAlloc_2050_, 5, v_newLocalDecls_2034_);
lean_ctor_set(v_reuseFailAlloc_2050_, 6, v_newLocalDeclsForMVars_2035_);
lean_ctor_set(v_reuseFailAlloc_2050_, 7, v_newLetDecls_2036_);
lean_ctor_set(v_reuseFailAlloc_2050_, 8, v_nextExprIdx_2037_);
lean_ctor_set(v_reuseFailAlloc_2050_, 9, v_exprMVarArgs_2038_);
lean_ctor_set(v_reuseFailAlloc_2050_, 10, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2050_, 11, v_toProcess_2040_);
v___x_2047_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_st_ref_put(v_a_2026_, v___x_2047_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2044_);
return v___x_2049_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_pushFVarArg___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2025_ = stack[0].m_obj;
lean_object* v_a_2026_ = stack[1].m_obj;
lean_object* v_res_2052_;
v_res_2052_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2025_, v_a_2026_);
stack->m_obj
 = v_res_2052_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object* v_e_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2053_, v_a_2054_);
lean_dec(v_a_2054_);
return v_res_2056_;
}
}
lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* v_e_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2057_, v_a_2059_);
return v___x_2065_;
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_pushFVarArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2057_ = stack[0].m_obj;
lean_object* v_a_2058_ = stack[1].m_obj;
lean_object* v_a_2059_ = stack[2].m_obj;
lean_object* v_a_2060_ = stack[3].m_obj;
lean_object* v_a_2061_ = stack[4].m_obj;
lean_object* v_a_2062_ = stack[5].m_obj;
lean_object* v_a_2063_ = stack[6].m_obj;
lean_object* v_res_2066_;
v_res_2066_ = l_Lean_Meta_Closure_pushFVarArg(v_e_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
stack->m_obj
 = v_res_2066_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* v_e_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_Meta_Closure_pushFVarArg(v_e_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
return v_res_2075_;
}
}
lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* v_newFVarId_2076_, lean_object* v_userName_2077_, lean_object* v_type_2078_, uint8_t v_bi_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Meta_Closure_collectExpr(v_type_2078_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2121_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2121_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2121_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v_visitedLevel_2093_; lean_object* v_visitedExpr_2094_; lean_object* v_levelParams_2095_; lean_object* v_nextLevelIdx_2096_; lean_object* v_levelArgs_2097_; lean_object* v_newLocalDecls_2098_; lean_object* v_newLocalDeclsForMVars_2099_; lean_object* v_newLetDecls_2100_; lean_object* v_nextExprIdx_2101_; lean_object* v_exprMVarArgs_2102_; lean_object* v_exprFVarArgs_2103_; lean_object* v_toProcess_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2120_; 
v___x_2092_ = lean_st_ref_take(v_a_2081_);
v_visitedLevel_2093_ = lean_ctor_get(v___x_2092_, 0);
v_visitedExpr_2094_ = lean_ctor_get(v___x_2092_, 1);
v_levelParams_2095_ = lean_ctor_get(v___x_2092_, 2);
v_nextLevelIdx_2096_ = lean_ctor_get(v___x_2092_, 3);
v_levelArgs_2097_ = lean_ctor_get(v___x_2092_, 4);
v_newLocalDecls_2098_ = lean_ctor_get(v___x_2092_, 5);
v_newLocalDeclsForMVars_2099_ = lean_ctor_get(v___x_2092_, 6);
v_newLetDecls_2100_ = lean_ctor_get(v___x_2092_, 7);
v_nextExprIdx_2101_ = lean_ctor_get(v___x_2092_, 8);
v_exprMVarArgs_2102_ = lean_ctor_get(v___x_2092_, 9);
v_exprFVarArgs_2103_ = lean_ctor_get(v___x_2092_, 10);
v_toProcess_2104_ = lean_ctor_get(v___x_2092_, 11);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2106_ = v___x_2092_;
v_isShared_2107_ = v_isSharedCheck_2120_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_toProcess_2104_);
lean_inc(v_exprFVarArgs_2103_);
lean_inc(v_exprMVarArgs_2102_);
lean_inc(v_nextExprIdx_2101_);
lean_inc(v_newLetDecls_2100_);
lean_inc(v_newLocalDeclsForMVars_2099_);
lean_inc(v_newLocalDecls_2098_);
lean_inc(v_levelArgs_2097_);
lean_inc(v_nextLevelIdx_2096_);
lean_inc(v_levelParams_2095_);
lean_inc(v_visitedExpr_2094_);
lean_inc(v_visitedLevel_2093_);
lean_dec(v___x_2092_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2120_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2108_ = lean_box(0);
v___x_2109_ = lean_unsigned_to_nat(0u);
v___x_2110_ = 0;
v___x_2111_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v_newFVarId_2076_);
lean_ctor_set(v___x_2111_, 2, v_userName_2077_);
lean_ctor_set(v___x_2111_, 3, v_a_2088_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*4, v_bi_2079_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*4 + 1, v___x_2110_);
v___x_2112_ = lean_array_push(v_newLocalDecls_2098_, v___x_2111_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 5, v___x_2112_);
v___x_2114_ = v___x_2106_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_visitedLevel_2093_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_visitedExpr_2094_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v_levelParams_2095_);
lean_ctor_set(v_reuseFailAlloc_2119_, 3, v_nextLevelIdx_2096_);
lean_ctor_set(v_reuseFailAlloc_2119_, 4, v_levelArgs_2097_);
lean_ctor_set(v_reuseFailAlloc_2119_, 5, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2119_, 6, v_newLocalDeclsForMVars_2099_);
lean_ctor_set(v_reuseFailAlloc_2119_, 7, v_newLetDecls_2100_);
lean_ctor_set(v_reuseFailAlloc_2119_, 8, v_nextExprIdx_2101_);
lean_ctor_set(v_reuseFailAlloc_2119_, 9, v_exprMVarArgs_2102_);
lean_ctor_set(v_reuseFailAlloc_2119_, 10, v_exprFVarArgs_2103_);
lean_ctor_set(v_reuseFailAlloc_2119_, 11, v_toProcess_2104_);
v___x_2114_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2115_ = lean_st_ref_put(v_a_2081_, v___x_2114_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2108_);
v___x_2117_ = v___x_2090_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2108_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_userName_2077_);
lean_dec(v_newFVarId_2076_);
v_a_2122_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2087_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2087_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_pushLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_newFVarId_2076_ = stack[0].m_obj;
lean_object* v_userName_2077_ = stack[1].m_obj;
lean_object* v_type_2078_ = stack[2].m_obj;
uint8_t v_bi_2079_ = stack[3].m_num;
lean_object* v_a_2080_ = stack[4].m_obj;
lean_object* v_a_2081_ = stack[5].m_obj;
lean_object* v_a_2082_ = stack[6].m_obj;
lean_object* v_a_2083_ = stack[7].m_obj;
lean_object* v_a_2084_ = stack[8].m_obj;
lean_object* v_a_2085_ = stack[9].m_obj;
lean_object* v_res_2130_;
v_res_2130_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2076_, v_userName_2077_, v_type_2078_, v_bi_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
stack->m_obj
 = v_res_2130_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* v_newFVarId_2131_, lean_object* v_userName_2132_, lean_object* v_type_2133_, lean_object* v_bi_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
uint8_t v_bi_boxed_2142_; lean_object* v_res_2143_; 
v_bi_boxed_2142_ = lean_unbox(v_bi_2134_);
v_res_2143_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2131_, v_userName_2132_, v_type_2133_, v_bi_boxed_2142_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
return v_res_2143_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(lean_object* v_k_2144_, lean_object* v_t_2145_){
_start:
{
if (lean_obj_tag(v_t_2145_) == 0)
{
lean_object* v_k_2146_; lean_object* v_l_2147_; lean_object* v_r_2148_; uint8_t v___x_2149_; 
v_k_2146_ = lean_ctor_get(v_t_2145_, 1);
v_l_2147_ = lean_ctor_get(v_t_2145_, 3);
v_r_2148_ = lean_ctor_get(v_t_2145_, 4);
v___x_2149_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2144_, v_k_2146_);
switch(v___x_2149_)
{
case 0:
{
v_t_2145_ = v_l_2147_;
goto _start;
}
case 1:
{
uint8_t v___x_2151_; 
v___x_2151_ = 1;
return v___x_2151_;
}
default: 
{
v_t_2145_ = v_r_2148_;
goto _start;
}
}
}
else
{
uint8_t v___x_2153_; 
v___x_2153_ = 0;
return v___x_2153_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2144_ = stack[0].m_obj;
lean_object* v_t_2145_ = stack[1].m_obj;
uint8_t v_res_2154_;
v_res_2154_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2144_, v_t_2145_);
stack->m_num = v_res_2154_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object* v_k_2155_, lean_object* v_t_2156_){
_start:
{
uint8_t v_res_2157_; lean_object* v_r_2158_; 
v_res_2157_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2155_, v_t_2156_);
lean_dec(v_t_2156_);
lean_dec(v_k_2155_);
v_r_2158_ = lean_box(v_res_2157_);
return v_r_2158_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(lean_object* v_newFVarId_2159_, lean_object* v_a_2160_, size_t v_sz_2161_, size_t v_i_2162_, lean_object* v_bs_2163_){
_start:
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_usize_dec_lt(v_i_2162_, v_sz_2161_);
if (v___x_2164_ == 0)
{
lean_dec(v_newFVarId_2159_);
return v_bs_2163_;
}
else
{
lean_object* v_v_2165_; lean_object* v___x_2166_; lean_object* v_bs_x27_2167_; lean_object* v___x_2168_; size_t v___x_2169_; size_t v___x_2170_; lean_object* v___x_2171_; 
v_v_2165_ = lean_array_uget(v_bs_2163_, v_i_2162_);
v___x_2166_ = lean_unsigned_to_nat(0u);
v_bs_x27_2167_ = lean_array_uset(v_bs_2163_, v_i_2162_, v___x_2166_);
lean_inc(v_newFVarId_2159_);
v___x_2168_ = l_Lean_LocalDecl_replaceFVarId(v_newFVarId_2159_, v_a_2160_, v_v_2165_);
v___x_2169_ = ((size_t)1ULL);
v___x_2170_ = lean_usize_add(v_i_2162_, v___x_2169_);
v___x_2171_ = lean_array_uset(v_bs_x27_2167_, v_i_2162_, v___x_2168_);
v_i_2162_ = v___x_2170_;
v_bs_2163_ = v___x_2171_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_newFVarId_2159_ = stack[0].m_obj;
lean_object* v_a_2160_ = stack[1].m_obj;
size_t v_sz_2161_ = stack[2].m_num;
size_t v_i_2162_ = stack[3].m_num;
lean_object* v_bs_2163_ = stack[4].m_obj;
lean_object* v_res_2173_;
v_res_2173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2159_, v_a_2160_, v_sz_2161_, v_i_2162_, v_bs_2163_);
stack->m_obj
 = v_res_2173_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(lean_object* v_newFVarId_2174_, lean_object* v_a_2175_, lean_object* v_sz_2176_, lean_object* v_i_2177_, lean_object* v_bs_2178_){
_start:
{
size_t v_sz_boxed_2179_; size_t v_i_boxed_2180_; lean_object* v_res_2181_; 
v_sz_boxed_2179_ = lean_unbox_usize(v_sz_2176_);
lean_dec(v_sz_2176_);
v_i_boxed_2180_ = lean_unbox_usize(v_i_2177_);
lean_dec(v_i_2177_);
v_res_2181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2174_, v_a_2175_, v_sz_boxed_2179_, v_i_boxed_2180_, v_bs_2178_);
lean_dec_ref(v_a_2175_);
return v_res_2181_;
}
}
lean_object* l_Lean_Meta_Closure_process(lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2183_, v_a_2184_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2317_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2317_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2317_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
if (lean_obj_tag(v_a_2190_) == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_box(0);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2194_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
else
{
lean_object* v_val_2198_; lean_object* v_fvarId_2199_; lean_object* v_newFVarId_2200_; lean_object* v___x_2201_; 
lean_del_object(v___x_2192_);
v_val_2198_ = lean_ctor_get(v_a_2190_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v_a_2190_, 1);
v_fvarId_2199_ = lean_ctor_get(v_val_2198_, 0);
lean_inc_n(v_fvarId_2199_, 2);
v_newFVarId_2200_ = lean_ctor_get(v_val_2198_, 1);
lean_inc(v_newFVarId_2200_);
lean_dec(v_val_2198_);
v___x_2201_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_2199_, v_a_2184_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
if (lean_obj_tag(v_a_2202_) == 0)
{
lean_object* v_userName_2203_; lean_object* v_type_2204_; uint8_t v_bi_2205_; lean_object* v___x_2206_; 
v_userName_2203_ = lean_ctor_get(v_a_2202_, 2);
lean_inc(v_userName_2203_);
v_type_2204_ = lean_ctor_get(v_a_2202_, 3);
lean_inc_ref(v_type_2204_);
v_bi_2205_ = lean_ctor_get_uint8(v_a_2202_, sizeof(void*)*4);
lean_dec_ref_known(v_a_2202_, 4);
v___x_2206_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2200_, v_userName_2203_, v_type_2204_, v_bi_2205_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec_ref_known(v___x_2206_, 1);
v___x_2207_ = l_Lean_mkFVar(v_fvarId_2199_);
v___x_2208_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2207_, v_a_2183_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_dec_ref_known(v___x_2208_, 1);
goto _start;
}
else
{
return v___x_2208_;
}
}
else
{
lean_dec(v_fvarId_2199_);
return v___x_2206_;
}
}
else
{
lean_object* v_userName_2210_; lean_object* v_type_2211_; lean_object* v_value_2212_; uint8_t v_nondep_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2306_; 
v_userName_2210_ = lean_ctor_get(v_a_2202_, 2);
v_type_2211_ = lean_ctor_get(v_a_2202_, 3);
v_value_2212_ = lean_ctor_get(v_a_2202_, 4);
v_nondep_2213_ = lean_ctor_get_uint8(v_a_2202_, sizeof(void*)*5);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_a_2202_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; lean_object* v_unused_2308_; 
v_unused_2307_ = lean_ctor_get(v_a_2202_, 1);
lean_dec(v_unused_2307_);
v_unused_2308_ = lean_ctor_get(v_a_2202_, 0);
lean_dec(v_unused_2308_);
v___x_2215_ = v_a_2202_;
v_isShared_2216_ = v_isSharedCheck_2306_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_value_2212_);
lean_inc(v_type_2211_);
lean_inc(v_userName_2210_);
lean_dec(v_a_2202_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2306_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v_a_2185_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
if (v_nondep_2213_ == 0)
{
uint8_t v___x_2225_; 
v___x_2225_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_fvarId_2199_, v_a_2218_);
lean_dec(v_a_2218_);
if (v___x_2225_ == 0)
{
lean_del_object(v___x_2215_);
lean_dec_ref(v_value_2212_);
goto v___jp_2219_;
}
else
{
lean_object* v___x_2226_; 
lean_dec(v_fvarId_2199_);
v___x_2226_ = l_Lean_Meta_Closure_collectExpr(v_type_2211_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2228_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v___x_2228_ = l_Lean_Meta_Closure_collectExpr(v_value_2212_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2230_; lean_object* v_visitedLevel_2231_; lean_object* v_visitedExpr_2232_; lean_object* v_levelParams_2233_; lean_object* v_nextLevelIdx_2234_; lean_object* v_levelArgs_2235_; lean_object* v_newLocalDecls_2236_; lean_object* v_newLocalDeclsForMVars_2237_; lean_object* v_newLetDecls_2238_; lean_object* v_nextExprIdx_2239_; lean_object* v_exprMVarArgs_2240_; lean_object* v_exprFVarArgs_2241_; lean_object* v_toProcess_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2281_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 1);
v___x_2230_ = lean_st_ref_take(v_a_2183_);
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
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2244_ = v___x_2230_;
v_isShared_2245_ = v_isSharedCheck_2281_;
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
v_isShared_2245_ = v_isSharedCheck_2281_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; uint8_t v___x_2247_; lean_object* v___x_2249_; 
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = 0;
lean_inc(v_a_2229_);
lean_inc(v_newFVarId_2200_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 4, v_a_2229_);
lean_ctor_set(v___x_2215_, 3, v_a_2227_);
lean_ctor_set(v___x_2215_, 1, v_newFVarId_2200_);
lean_ctor_set(v___x_2215_, 0, v___x_2246_);
v___x_2249_ = v___x_2215_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_newFVarId_2200_);
lean_ctor_set(v_reuseFailAlloc_2280_, 2, v_userName_2210_);
lean_ctor_set(v_reuseFailAlloc_2280_, 3, v_a_2227_);
lean_ctor_set(v_reuseFailAlloc_2280_, 4, v_a_2229_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*5, v_nondep_2213_);
v___x_2249_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*5 + 1, v___x_2247_);
v___x_2250_ = lean_array_push(v_newLetDecls_2238_, v___x_2249_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 7, v___x_2250_);
v___x_2252_ = v___x_2244_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_visitedLevel_2231_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_visitedExpr_2232_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_levelParams_2233_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v_nextLevelIdx_2234_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v_levelArgs_2235_);
lean_ctor_set(v_reuseFailAlloc_2279_, 5, v_newLocalDecls_2236_);
lean_ctor_set(v_reuseFailAlloc_2279_, 6, v_newLocalDeclsForMVars_2237_);
lean_ctor_set(v_reuseFailAlloc_2279_, 7, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2279_, 8, v_nextExprIdx_2239_);
lean_ctor_set(v_reuseFailAlloc_2279_, 9, v_exprMVarArgs_2240_);
lean_ctor_set(v_reuseFailAlloc_2279_, 10, v_exprFVarArgs_2241_);
lean_ctor_set(v_reuseFailAlloc_2279_, 11, v_toProcess_2242_);
v___x_2252_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_visitedLevel_2255_; lean_object* v_visitedExpr_2256_; lean_object* v_levelParams_2257_; lean_object* v_nextLevelIdx_2258_; lean_object* v_levelArgs_2259_; lean_object* v_newLocalDecls_2260_; lean_object* v_newLocalDeclsForMVars_2261_; lean_object* v_newLetDecls_2262_; lean_object* v_nextExprIdx_2263_; lean_object* v_exprMVarArgs_2264_; lean_object* v_exprFVarArgs_2265_; lean_object* v_toProcess_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2278_; 
v___x_2253_ = lean_st_ref_put(v_a_2183_, v___x_2252_);
v___x_2254_ = lean_st_ref_take(v_a_2183_);
v_visitedLevel_2255_ = lean_ctor_get(v___x_2254_, 0);
v_visitedExpr_2256_ = lean_ctor_get(v___x_2254_, 1);
v_levelParams_2257_ = lean_ctor_get(v___x_2254_, 2);
v_nextLevelIdx_2258_ = lean_ctor_get(v___x_2254_, 3);
v_levelArgs_2259_ = lean_ctor_get(v___x_2254_, 4);
v_newLocalDecls_2260_ = lean_ctor_get(v___x_2254_, 5);
v_newLocalDeclsForMVars_2261_ = lean_ctor_get(v___x_2254_, 6);
v_newLetDecls_2262_ = lean_ctor_get(v___x_2254_, 7);
v_nextExprIdx_2263_ = lean_ctor_get(v___x_2254_, 8);
v_exprMVarArgs_2264_ = lean_ctor_get(v___x_2254_, 9);
v_exprFVarArgs_2265_ = lean_ctor_get(v___x_2254_, 10);
v_toProcess_2266_ = lean_ctor_get(v___x_2254_, 11);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2268_ = v___x_2254_;
v_isShared_2269_ = v_isSharedCheck_2278_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_toProcess_2266_);
lean_inc(v_exprFVarArgs_2265_);
lean_inc(v_exprMVarArgs_2264_);
lean_inc(v_nextExprIdx_2263_);
lean_inc(v_newLetDecls_2262_);
lean_inc(v_newLocalDeclsForMVars_2261_);
lean_inc(v_newLocalDecls_2260_);
lean_inc(v_levelArgs_2259_);
lean_inc(v_nextLevelIdx_2258_);
lean_inc(v_levelParams_2257_);
lean_inc(v_visitedExpr_2256_);
lean_inc(v_visitedLevel_2255_);
lean_dec(v___x_2254_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2278_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
size_t v_sz_2270_; size_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
v_sz_2270_ = lean_array_size(v_newLocalDecls_2260_);
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2200_, v_a_2229_, v_sz_2270_, v___x_2271_, v_newLocalDecls_2260_);
lean_dec(v_a_2229_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 5, v___x_2272_);
v___x_2274_ = v___x_2268_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_visitedLevel_2255_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_visitedExpr_2256_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v_levelParams_2257_);
lean_ctor_set(v_reuseFailAlloc_2277_, 3, v_nextLevelIdx_2258_);
lean_ctor_set(v_reuseFailAlloc_2277_, 4, v_levelArgs_2259_);
lean_ctor_set(v_reuseFailAlloc_2277_, 5, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2277_, 6, v_newLocalDeclsForMVars_2261_);
lean_ctor_set(v_reuseFailAlloc_2277_, 7, v_newLetDecls_2262_);
lean_ctor_set(v_reuseFailAlloc_2277_, 8, v_nextExprIdx_2263_);
lean_ctor_set(v_reuseFailAlloc_2277_, 9, v_exprMVarArgs_2264_);
lean_ctor_set(v_reuseFailAlloc_2277_, 10, v_exprFVarArgs_2265_);
lean_ctor_set(v_reuseFailAlloc_2277_, 11, v_toProcess_2266_);
v___x_2274_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2275_; 
v___x_2275_ = lean_st_ref_put(v_a_2183_, v___x_2274_);
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v_a_2227_);
lean_del_object(v___x_2215_);
lean_dec(v_userName_2210_);
lean_dec(v_newFVarId_2200_);
v_a_2282_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2228_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2228_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_del_object(v___x_2215_);
lean_dec_ref(v_value_2212_);
lean_dec(v_userName_2210_);
lean_dec(v_newFVarId_2200_);
v_a_2290_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2226_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2226_);
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
else
{
lean_dec(v_a_2218_);
lean_del_object(v___x_2215_);
lean_dec_ref(v_value_2212_);
goto v___jp_2219_;
}
v___jp_2219_:
{
uint8_t v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = 0;
v___x_2221_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2200_, v_userName_2210_, v_type_2211_, v___x_2220_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec_ref_known(v___x_2221_, 1);
v___x_2222_ = l_Lean_mkFVar(v_fvarId_2199_);
v___x_2223_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2222_, v_a_2183_);
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
lean_dec(v_fvarId_2199_);
return v___x_2221_;
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_del_object(v___x_2215_);
lean_dec_ref(v_value_2212_);
lean_dec_ref(v_type_2211_);
lean_dec(v_userName_2210_);
lean_dec(v_newFVarId_2200_);
lean_dec(v_fvarId_2199_);
v_a_2298_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2217_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2217_);
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
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec(v_newFVarId_2200_);
lean_dec(v_fvarId_2199_);
v_a_2309_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2201_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2201_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
v_a_2318_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2189_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2189_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_process_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2182_ = stack[0].m_obj;
lean_object* v_a_2183_ = stack[1].m_obj;
lean_object* v_a_2184_ = stack[2].m_obj;
lean_object* v_a_2185_ = stack[3].m_obj;
lean_object* v_a_2186_ = stack[4].m_obj;
lean_object* v_a_2187_ = stack[5].m_obj;
lean_object* v_res_2326_;
v_res_2326_ = l_Lean_Meta_Closure_process(v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
stack->m_obj
 = v_res_2326_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_Meta_Closure_process(v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
return v_res_2334_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(lean_object* v_00_u03b2_2335_, lean_object* v_k_2336_, lean_object* v_t_2337_){
_start:
{
uint8_t v___x_2338_; 
v___x_2338_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2336_, v_t_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2336_ = stack[1].m_obj;
lean_object* v_t_2337_ = stack[2].m_obj;
uint8_t v_res_2339_;
v_res_2339_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(lean_box(0), v_k_2336_, v_t_2337_);
stack->m_num = v_res_2339_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___boxed(lean_object* v_00_u03b2_2340_, lean_object* v_k_2341_, lean_object* v_t_2342_){
_start:
{
uint8_t v_res_2343_; lean_object* v_r_2344_; 
v_res_2343_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(v_00_u03b2_2340_, v_k_2341_, v_t_2342_);
lean_dec(v_t_2342_);
lean_dec(v_k_2341_);
v_r_2344_ = lean_box(v_res_2343_);
return v_r_2344_;
}
}
lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object* v_decls_2345_, lean_object* v_xs_2346_, uint8_t v_isLambda_2347_, lean_object* v_i_2348_, lean_object* v_x_2349_, lean_object* v_b_2350_){
_start:
{
lean_object* v_decl_2351_; 
v_decl_2351_ = lean_array_fget_borrowed(v_decls_2345_, v_i_2348_);
if (lean_obj_tag(v_decl_2351_) == 0)
{
lean_object* v_userName_2352_; lean_object* v_type_2353_; uint8_t v_bi_2354_; lean_object* v_ty_2355_; 
v_userName_2352_ = lean_ctor_get(v_decl_2351_, 2);
v_type_2353_ = lean_ctor_get(v_decl_2351_, 3);
v_bi_2354_ = lean_ctor_get_uint8(v_decl_2351_, sizeof(void*)*4);
v_ty_2355_ = lean_expr_abstract_range(v_type_2353_, v_i_2348_, v_xs_2346_);
if (v_isLambda_2347_ == 0)
{
lean_object* v___x_2356_; 
lean_inc(v_userName_2352_);
v___x_2356_ = l_Lean_mkForall(v_userName_2352_, v_bi_2354_, v_ty_2355_, v_b_2350_);
return v___x_2356_;
}
else
{
lean_object* v___x_2357_; 
lean_inc(v_userName_2352_);
v___x_2357_ = l_Lean_mkLambda(v_userName_2352_, v_bi_2354_, v_ty_2355_, v_b_2350_);
return v___x_2357_;
}
}
else
{
lean_object* v_userName_2358_; lean_object* v_type_2359_; lean_object* v_value_2360_; uint8_t v_nondep_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v_userName_2358_ = lean_ctor_get(v_decl_2351_, 2);
v_type_2359_ = lean_ctor_get(v_decl_2351_, 3);
v_value_2360_ = lean_ctor_get(v_decl_2351_, 4);
v_nondep_2361_ = lean_ctor_get_uint8(v_decl_2351_, sizeof(void*)*5);
v___x_2362_ = lean_unsigned_to_nat(0u);
v___x_2363_ = lean_expr_has_loose_bvar(v_b_2350_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = lean_expr_lower_loose_bvars(v_b_2350_, v___x_2364_, v___x_2364_);
lean_dec_ref(v_b_2350_);
return v___x_2365_;
}
else
{
lean_object* v_ty_2366_; lean_object* v_val_2367_; lean_object* v___x_2368_; 
v_ty_2366_ = lean_expr_abstract_range(v_type_2359_, v_i_2348_, v_xs_2346_);
v_val_2367_ = lean_expr_abstract_range(v_value_2360_, v_i_2348_, v_xs_2346_);
lean_inc(v_userName_2358_);
v___x_2368_ = l_Lean_Expr_letE___override(v_userName_2358_, v_ty_2366_, v_val_2367_, v_b_2350_, v_nondep_2361_);
return v___x_2368_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_mkBinding___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_2345_ = stack[0].m_obj;
lean_object* v_xs_2346_ = stack[1].m_obj;
uint8_t v_isLambda_2347_ = stack[2].m_num;
lean_object* v_i_2348_ = stack[3].m_obj;
lean_object* v_b_2350_ = stack[5].m_obj;
lean_object* v_res_2369_;
v_res_2369_ = l_Lean_Meta_Closure_mkBinding___lam__0(v_decls_2345_, v_xs_2346_, v_isLambda_2347_, v_i_2348_, lean_box(0), v_b_2350_);
stack->m_obj
 = v_res_2369_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object* v_decls_2370_, lean_object* v_xs_2371_, lean_object* v_isLambda_2372_, lean_object* v_i_2373_, lean_object* v_x_2374_, lean_object* v_b_2375_){
_start:
{
uint8_t v_isLambda_boxed_2376_; lean_object* v_res_2377_; 
v_isLambda_boxed_2376_ = lean_unbox(v_isLambda_2372_);
v_res_2377_ = l_Lean_Meta_Closure_mkBinding___lam__0(v_decls_2370_, v_xs_2371_, v_isLambda_boxed_2376_, v_i_2373_, v_x_2374_, v_b_2375_);
lean_dec(v_i_2373_);
lean_dec_ref(v_xs_2371_);
lean_dec_ref(v_decls_2370_);
return v_res_2377_;
}
}
lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t v_isLambda_2398_, lean_object* v_decls_2399_, lean_object* v_b_2400_){
_start:
{
lean_object* v___f_2401_; lean_object* v___x_2402_; size_t v_sz_2403_; size_t v___x_2404_; lean_object* v_xs_2405_; lean_object* v___x_2406_; lean_object* v___f_2407_; lean_object* v_b_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___f_2401_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__0));
v___x_2402_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__10));
v_sz_2403_ = lean_array_size(v_decls_2399_);
v___x_2404_ = ((size_t)0ULL);
lean_inc_ref_n(v_decls_2399_, 2);
v_xs_2405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2402_, v___f_2401_, v_sz_2403_, v___x_2404_, v_decls_2399_);
v___x_2406_ = lean_box(v_isLambda_2398_);
lean_inc(v_xs_2405_);
v___f_2407_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2407_, 0, v_decls_2399_);
lean_closure_set(v___f_2407_, 1, v_xs_2405_);
lean_closure_set(v___f_2407_, 2, v___x_2406_);
v_b_2408_ = lean_expr_abstract(v_b_2400_, v_xs_2405_);
lean_dec(v_xs_2405_);
v___x_2409_ = lean_array_get_size(v_decls_2399_);
lean_dec_ref(v_decls_2399_);
v___x_2410_ = l_Nat_foldRev___redArg(v___x_2409_, v___f_2407_, v_b_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_mkBinding_0interp(lean_interpreter_value* stack)
{
uint8_t v_isLambda_2398_ = stack[0].m_num;
lean_object* v_decls_2399_ = stack[1].m_obj;
lean_object* v_b_2400_ = stack[2].m_obj;
lean_object* v_res_2411_;
v_res_2411_ = l_Lean_Meta_Closure_mkBinding(v_isLambda_2398_, v_decls_2399_, v_b_2400_);
stack->m_obj
 = v_res_2411_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* v_isLambda_2412_, lean_object* v_decls_2413_, lean_object* v_b_2414_){
_start:
{
uint8_t v_isLambda_boxed_2415_; lean_object* v_res_2416_; 
v_isLambda_boxed_2415_ = lean_unbox(v_isLambda_2412_);
v_res_2416_ = l_Lean_Meta_Closure_mkBinding(v_isLambda_boxed_2415_, v_decls_2413_, v_b_2414_);
lean_dec_ref(v_b_2414_);
return v_res_2416_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(size_t v_sz_2417_, size_t v_i_2418_, lean_object* v_bs_2419_){
_start:
{
uint8_t v___x_2420_; 
v___x_2420_ = lean_usize_dec_lt(v_i_2418_, v_sz_2417_);
if (v___x_2420_ == 0)
{
return v_bs_2419_;
}
else
{
lean_object* v_v_2421_; lean_object* v___x_2422_; lean_object* v_bs_x27_2423_; lean_object* v___x_2424_; size_t v___x_2425_; size_t v___x_2426_; lean_object* v___x_2427_; 
v_v_2421_ = lean_array_uget(v_bs_2419_, v_i_2418_);
v___x_2422_ = lean_unsigned_to_nat(0u);
v_bs_x27_2423_ = lean_array_uset(v_bs_2419_, v_i_2418_, v___x_2422_);
v___x_2424_ = l_Lean_LocalDecl_toExpr(v_v_2421_);
v___x_2425_ = ((size_t)1ULL);
v___x_2426_ = lean_usize_add(v_i_2418_, v___x_2425_);
v___x_2427_ = lean_array_uset(v_bs_x27_2423_, v_i_2418_, v___x_2424_);
v_i_2418_ = v___x_2426_;
v_bs_2419_ = v___x_2427_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2417_ = stack[0].m_num;
size_t v_i_2418_ = stack[1].m_num;
lean_object* v_bs_2419_ = stack[2].m_obj;
lean_object* v_res_2429_;
v_res_2429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2417_, v_i_2418_, v_bs_2419_);
stack->m_obj
 = v_res_2429_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object* v_sz_2430_, lean_object* v_i_2431_, lean_object* v_bs_2432_){
_start:
{
size_t v_sz_boxed_2433_; size_t v_i_boxed_2434_; lean_object* v_res_2435_; 
v_sz_boxed_2433_ = lean_unbox_usize(v_sz_2430_);
lean_dec(v_sz_2430_);
v_i_boxed_2434_ = lean_unbox_usize(v_i_2431_);
lean_dec(v_i_2431_);
v_res_2435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_boxed_2433_, v_i_boxed_2434_, v_bs_2432_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object* v_decls_2436_, lean_object* v_xs_2437_, lean_object* v_x_2438_, lean_object* v_x_2439_){
_start:
{
lean_object* v_zero_2440_; uint8_t v_isZero_2441_; 
v_zero_2440_ = lean_unsigned_to_nat(0u);
v_isZero_2441_ = lean_nat_dec_eq(v_x_2438_, v_zero_2440_);
if (v_isZero_2441_ == 1)
{
lean_dec(v_x_2438_);
return v_x_2439_;
}
else
{
lean_object* v_one_2442_; lean_object* v_n_2443_; lean_object* v_decl_2444_; 
v_one_2442_ = lean_unsigned_to_nat(1u);
v_n_2443_ = lean_nat_sub(v_x_2438_, v_one_2442_);
lean_dec(v_x_2438_);
v_decl_2444_ = lean_array_fget_borrowed(v_decls_2436_, v_n_2443_);
if (lean_obj_tag(v_decl_2444_) == 0)
{
lean_object* v_userName_2445_; lean_object* v_type_2446_; uint8_t v_bi_2447_; lean_object* v_ty_2448_; lean_object* v___x_2449_; 
v_userName_2445_ = lean_ctor_get(v_decl_2444_, 2);
v_type_2446_ = lean_ctor_get(v_decl_2444_, 3);
v_bi_2447_ = lean_ctor_get_uint8(v_decl_2444_, sizeof(void*)*4);
v_ty_2448_ = lean_expr_abstract_range(v_type_2446_, v_n_2443_, v_xs_2437_);
lean_inc(v_userName_2445_);
v___x_2449_ = l_Lean_mkLambda(v_userName_2445_, v_bi_2447_, v_ty_2448_, v_x_2439_);
v_x_2438_ = v_n_2443_;
v_x_2439_ = v___x_2449_;
goto _start;
}
else
{
lean_object* v_userName_2451_; lean_object* v_type_2452_; lean_object* v_value_2453_; uint8_t v_nondep_2454_; uint8_t v___x_2455_; 
v_userName_2451_ = lean_ctor_get(v_decl_2444_, 2);
v_type_2452_ = lean_ctor_get(v_decl_2444_, 3);
v_value_2453_ = lean_ctor_get(v_decl_2444_, 4);
v_nondep_2454_ = lean_ctor_get_uint8(v_decl_2444_, sizeof(void*)*5);
v___x_2455_ = lean_expr_has_loose_bvar(v_x_2439_, v_zero_2440_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_expr_lower_loose_bvars(v_x_2439_, v_one_2442_, v_one_2442_);
lean_dec_ref(v_x_2439_);
v_x_2438_ = v_n_2443_;
v_x_2439_ = v___x_2456_;
goto _start;
}
else
{
lean_object* v_ty_2458_; lean_object* v_val_2459_; lean_object* v___x_2460_; 
v_ty_2458_ = lean_expr_abstract_range(v_type_2452_, v_n_2443_, v_xs_2437_);
v_val_2459_ = lean_expr_abstract_range(v_value_2453_, v_n_2443_, v_xs_2437_);
lean_inc(v_userName_2451_);
v___x_2460_ = l_Lean_Expr_letE___override(v_userName_2451_, v_ty_2458_, v_val_2459_, v_x_2439_, v_nondep_2454_);
v_x_2438_ = v_n_2443_;
v_x_2439_ = v___x_2460_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1___boxed(lean_object* v_decls_2462_, lean_object* v_xs_2463_, lean_object* v_x_2464_, lean_object* v_x_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2462_, v_xs_2463_, v_x_2464_, v_x_2465_);
lean_dec_ref(v_xs_2463_);
lean_dec_ref(v_decls_2462_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(lean_object* v_decls_2467_, lean_object* v_xs_2468_, lean_object* v_x_2469_, lean_object* v_x_2470_){
_start:
{
lean_object* v_zero_2471_; uint8_t v_isZero_2472_; 
v_zero_2471_ = lean_unsigned_to_nat(0u);
v_isZero_2472_ = lean_nat_dec_eq(v_x_2469_, v_zero_2471_);
if (v_isZero_2472_ == 1)
{
return v_x_2470_;
}
else
{
lean_object* v_one_2473_; lean_object* v_n_2474_; lean_object* v_decl_2475_; 
v_one_2473_ = lean_unsigned_to_nat(1u);
v_n_2474_ = lean_nat_sub(v_x_2469_, v_one_2473_);
v_decl_2475_ = lean_array_fget_borrowed(v_decls_2467_, v_n_2474_);
if (lean_obj_tag(v_decl_2475_) == 0)
{
lean_object* v_userName_2476_; lean_object* v_type_2477_; uint8_t v_bi_2478_; lean_object* v_ty_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_userName_2476_ = lean_ctor_get(v_decl_2475_, 2);
v_type_2477_ = lean_ctor_get(v_decl_2475_, 3);
v_bi_2478_ = lean_ctor_get_uint8(v_decl_2475_, sizeof(void*)*4);
v_ty_2479_ = lean_expr_abstract_range(v_type_2477_, v_n_2474_, v_xs_2468_);
lean_inc(v_userName_2476_);
v___x_2480_ = l_Lean_mkLambda(v_userName_2476_, v_bi_2478_, v_ty_2479_, v_x_2470_);
v___x_2481_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2467_, v_xs_2468_, v_n_2474_, v___x_2480_);
return v___x_2481_;
}
else
{
lean_object* v_userName_2482_; lean_object* v_type_2483_; lean_object* v_value_2484_; uint8_t v_nondep_2485_; uint8_t v___x_2486_; 
v_userName_2482_ = lean_ctor_get(v_decl_2475_, 2);
v_type_2483_ = lean_ctor_get(v_decl_2475_, 3);
v_value_2484_ = lean_ctor_get(v_decl_2475_, 4);
v_nondep_2485_ = lean_ctor_get_uint8(v_decl_2475_, sizeof(void*)*5);
v___x_2486_ = lean_expr_has_loose_bvar(v_x_2470_, v_zero_2471_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = lean_expr_lower_loose_bvars(v_x_2470_, v_one_2473_, v_one_2473_);
lean_dec_ref(v_x_2470_);
v___x_2488_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2467_, v_xs_2468_, v_n_2474_, v___x_2487_);
return v___x_2488_;
}
else
{
lean_object* v_ty_2489_; lean_object* v_val_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v_ty_2489_ = lean_expr_abstract_range(v_type_2483_, v_n_2474_, v_xs_2468_);
v_val_2490_ = lean_expr_abstract_range(v_value_2484_, v_n_2474_, v_xs_2468_);
lean_inc(v_userName_2482_);
v___x_2491_ = l_Lean_Expr_letE___override(v_userName_2482_, v_ty_2489_, v_val_2490_, v_x_2470_, v_nondep_2485_);
v___x_2492_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2467_, v_xs_2468_, v_n_2474_, v___x_2491_);
return v___x_2492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object* v_decls_2493_, lean_object* v_xs_2494_, lean_object* v_x_2495_, lean_object* v_x_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2493_, v_xs_2494_, v_x_2495_, v_x_2496_);
lean_dec(v_x_2495_);
lean_dec_ref(v_xs_2494_);
lean_dec_ref(v_decls_2493_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* v_decls_2498_, lean_object* v_b_2499_){
_start:
{
size_t v_sz_2500_; size_t v___x_2501_; lean_object* v_xs_2502_; lean_object* v_b_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_sz_2500_ = lean_array_size(v_decls_2498_);
v___x_2501_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2498_);
v_xs_2502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2500_, v___x_2501_, v_decls_2498_);
v_b_2503_ = lean_expr_abstract(v_b_2499_, v_xs_2502_);
v___x_2504_ = lean_array_get_size(v_decls_2498_);
v___x_2505_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2498_, v_xs_2502_, v___x_2504_, v_b_2503_);
lean_dec_ref(v_xs_2502_);
lean_dec_ref(v_decls_2498_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* v_decls_2506_, lean_object* v_b_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Meta_Closure_mkLambda(v_decls_2506_, v_b_2507_);
lean_dec_ref(v_b_2507_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(lean_object* v_decls_2509_, lean_object* v_xs_2510_, lean_object* v_x_2511_, lean_object* v_x_2512_){
_start:
{
lean_object* v_zero_2513_; uint8_t v_isZero_2514_; 
v_zero_2513_ = lean_unsigned_to_nat(0u);
v_isZero_2514_ = lean_nat_dec_eq(v_x_2511_, v_zero_2513_);
if (v_isZero_2514_ == 1)
{
lean_dec(v_x_2511_);
return v_x_2512_;
}
else
{
lean_object* v_one_2515_; lean_object* v_n_2516_; lean_object* v_decl_2517_; 
v_one_2515_ = lean_unsigned_to_nat(1u);
v_n_2516_ = lean_nat_sub(v_x_2511_, v_one_2515_);
lean_dec(v_x_2511_);
v_decl_2517_ = lean_array_fget_borrowed(v_decls_2509_, v_n_2516_);
if (lean_obj_tag(v_decl_2517_) == 0)
{
lean_object* v_userName_2518_; lean_object* v_type_2519_; uint8_t v_bi_2520_; lean_object* v_ty_2521_; lean_object* v___x_2522_; 
v_userName_2518_ = lean_ctor_get(v_decl_2517_, 2);
v_type_2519_ = lean_ctor_get(v_decl_2517_, 3);
v_bi_2520_ = lean_ctor_get_uint8(v_decl_2517_, sizeof(void*)*4);
v_ty_2521_ = lean_expr_abstract_range(v_type_2519_, v_n_2516_, v_xs_2510_);
lean_inc(v_userName_2518_);
v___x_2522_ = l_Lean_mkForall(v_userName_2518_, v_bi_2520_, v_ty_2521_, v_x_2512_);
v_x_2511_ = v_n_2516_;
v_x_2512_ = v___x_2522_;
goto _start;
}
else
{
lean_object* v_userName_2524_; lean_object* v_type_2525_; lean_object* v_value_2526_; uint8_t v_nondep_2527_; uint8_t v___x_2528_; 
v_userName_2524_ = lean_ctor_get(v_decl_2517_, 2);
v_type_2525_ = lean_ctor_get(v_decl_2517_, 3);
v_value_2526_ = lean_ctor_get(v_decl_2517_, 4);
v_nondep_2527_ = lean_ctor_get_uint8(v_decl_2517_, sizeof(void*)*5);
v___x_2528_ = lean_expr_has_loose_bvar(v_x_2512_, v_zero_2513_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_expr_lower_loose_bvars(v_x_2512_, v_one_2515_, v_one_2515_);
lean_dec_ref(v_x_2512_);
v_x_2511_ = v_n_2516_;
v_x_2512_ = v___x_2529_;
goto _start;
}
else
{
lean_object* v_ty_2531_; lean_object* v_val_2532_; lean_object* v___x_2533_; 
v_ty_2531_ = lean_expr_abstract_range(v_type_2525_, v_n_2516_, v_xs_2510_);
v_val_2532_ = lean_expr_abstract_range(v_value_2526_, v_n_2516_, v_xs_2510_);
lean_inc(v_userName_2524_);
v___x_2533_ = l_Lean_Expr_letE___override(v_userName_2524_, v_ty_2531_, v_val_2532_, v_x_2512_, v_nondep_2527_);
v_x_2511_ = v_n_2516_;
v_x_2512_ = v___x_2533_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0___boxed(lean_object* v_decls_2535_, lean_object* v_xs_2536_, lean_object* v_x_2537_, lean_object* v_x_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2535_, v_xs_2536_, v_x_2537_, v_x_2538_);
lean_dec_ref(v_xs_2536_);
lean_dec_ref(v_decls_2535_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(lean_object* v_decls_2540_, lean_object* v_xs_2541_, lean_object* v_x_2542_, lean_object* v_x_2543_){
_start:
{
lean_object* v_zero_2544_; uint8_t v_isZero_2545_; 
v_zero_2544_ = lean_unsigned_to_nat(0u);
v_isZero_2545_ = lean_nat_dec_eq(v_x_2542_, v_zero_2544_);
if (v_isZero_2545_ == 1)
{
return v_x_2543_;
}
else
{
lean_object* v_one_2546_; lean_object* v_n_2547_; lean_object* v_decl_2548_; 
v_one_2546_ = lean_unsigned_to_nat(1u);
v_n_2547_ = lean_nat_sub(v_x_2542_, v_one_2546_);
v_decl_2548_ = lean_array_fget_borrowed(v_decls_2540_, v_n_2547_);
if (lean_obj_tag(v_decl_2548_) == 0)
{
lean_object* v_userName_2549_; lean_object* v_type_2550_; uint8_t v_bi_2551_; lean_object* v_ty_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_userName_2549_ = lean_ctor_get(v_decl_2548_, 2);
v_type_2550_ = lean_ctor_get(v_decl_2548_, 3);
v_bi_2551_ = lean_ctor_get_uint8(v_decl_2548_, sizeof(void*)*4);
v_ty_2552_ = lean_expr_abstract_range(v_type_2550_, v_n_2547_, v_xs_2541_);
lean_inc(v_userName_2549_);
v___x_2553_ = l_Lean_mkForall(v_userName_2549_, v_bi_2551_, v_ty_2552_, v_x_2543_);
v___x_2554_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2540_, v_xs_2541_, v_n_2547_, v___x_2553_);
return v___x_2554_;
}
else
{
lean_object* v_userName_2555_; lean_object* v_type_2556_; lean_object* v_value_2557_; uint8_t v_nondep_2558_; uint8_t v___x_2559_; 
v_userName_2555_ = lean_ctor_get(v_decl_2548_, 2);
v_type_2556_ = lean_ctor_get(v_decl_2548_, 3);
v_value_2557_ = lean_ctor_get(v_decl_2548_, 4);
v_nondep_2558_ = lean_ctor_get_uint8(v_decl_2548_, sizeof(void*)*5);
v___x_2559_ = lean_expr_has_loose_bvar(v_x_2543_, v_zero_2544_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = lean_expr_lower_loose_bvars(v_x_2543_, v_one_2546_, v_one_2546_);
lean_dec_ref(v_x_2543_);
v___x_2561_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2540_, v_xs_2541_, v_n_2547_, v___x_2560_);
return v___x_2561_;
}
else
{
lean_object* v_ty_2562_; lean_object* v_val_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v_ty_2562_ = lean_expr_abstract_range(v_type_2556_, v_n_2547_, v_xs_2541_);
v_val_2563_ = lean_expr_abstract_range(v_value_2557_, v_n_2547_, v_xs_2541_);
lean_inc(v_userName_2555_);
v___x_2564_ = l_Lean_Expr_letE___override(v_userName_2555_, v_ty_2562_, v_val_2563_, v_x_2543_, v_nondep_2558_);
v___x_2565_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2540_, v_xs_2541_, v_n_2547_, v___x_2564_);
return v___x_2565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object* v_decls_2566_, lean_object* v_xs_2567_, lean_object* v_x_2568_, lean_object* v_x_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2566_, v_xs_2567_, v_x_2568_, v_x_2569_);
lean_dec(v_x_2568_);
lean_dec_ref(v_xs_2567_);
lean_dec_ref(v_decls_2566_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* v_decls_2571_, lean_object* v_b_2572_){
_start:
{
size_t v_sz_2573_; size_t v___x_2574_; lean_object* v_xs_2575_; lean_object* v_b_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_sz_2573_ = lean_array_size(v_decls_2571_);
v___x_2574_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2571_);
v_xs_2575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2573_, v___x_2574_, v_decls_2571_);
v_b_2576_ = lean_expr_abstract(v_b_2572_, v_xs_2575_);
v___x_2577_ = lean_array_get_size(v_decls_2571_);
v___x_2578_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2571_, v_xs_2575_, v___x_2577_, v_b_2576_);
lean_dec_ref(v_xs_2575_);
lean_dec_ref(v_decls_2571_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* v_decls_2579_, lean_object* v_b_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_Meta_Closure_mkForall(v_decls_2579_, v_b_2580_);
lean_dec_ref(v_b_2580_);
return v_res_2581_;
}
}
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object* v_a_2582_, lean_object* v_cache_2583_, lean_object* v_a_x3f_2584_){
_start:
{
lean_object* v___x_2586_; lean_object* v_mctx_2587_; lean_object* v_zetaDeltaFVarIds_2588_; lean_object* v_postponed_2589_; lean_object* v_diag_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2600_; 
v___x_2586_ = lean_st_ref_take(v_a_2582_);
v_mctx_2587_ = lean_ctor_get(v___x_2586_, 0);
v_zetaDeltaFVarIds_2588_ = lean_ctor_get(v___x_2586_, 2);
v_postponed_2589_ = lean_ctor_get(v___x_2586_, 3);
v_diag_2590_ = lean_ctor_get(v___x_2586_, 4);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; 
v_unused_2601_ = lean_ctor_get(v___x_2586_, 1);
lean_dec(v_unused_2601_);
v___x_2592_ = v___x_2586_;
v_isShared_2593_ = v_isSharedCheck_2600_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_diag_2590_);
lean_inc(v_postponed_2589_);
lean_inc(v_zetaDeltaFVarIds_2588_);
lean_inc(v_mctx_2587_);
lean_dec(v___x_2586_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2600_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2594_ = lean_box(0);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 1, v_cache_2583_);
v___x_2596_ = v___x_2592_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_mctx_2587_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_cache_2583_);
lean_ctor_set(v_reuseFailAlloc_2599_, 2, v_zetaDeltaFVarIds_2588_);
lean_ctor_set(v_reuseFailAlloc_2599_, 3, v_postponed_2589_);
lean_ctor_set(v_reuseFailAlloc_2599_, 4, v_diag_2590_);
v___x_2596_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = lean_st_ref_put(v_a_2582_, v___x_2596_);
v___x_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2594_);
return v___x_2598_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2582_ = stack[0].m_obj;
lean_object* v_cache_2583_ = stack[1].m_obj;
lean_object* v_a_x3f_2584_ = stack[2].m_obj;
lean_object* v_res_2602_;
v_res_2602_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2582_, v_cache_2583_, v_a_x3f_2584_);
stack->m_obj
 = v_res_2602_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object* v_a_2603_, lean_object* v_cache_2604_, lean_object* v_a_x3f_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2603_, v_cache_2604_, v_a_x3f_2605_);
lean_dec(v_a_x3f_2605_);
lean_dec(v_a_2603_);
return v_res_2607_;
}
}
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object* v_a_2608_, lean_object* v_zetaDeltaFVarIds_2609_, lean_object* v_a_x3f_2610_){
_start:
{
lean_object* v___x_2612_; lean_object* v_mctx_2613_; lean_object* v_cache_2614_; lean_object* v_postponed_2615_; lean_object* v_diag_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2626_; 
v___x_2612_ = lean_st_ref_take(v_a_2608_);
v_mctx_2613_ = lean_ctor_get(v___x_2612_, 0);
v_cache_2614_ = lean_ctor_get(v___x_2612_, 1);
v_postponed_2615_ = lean_ctor_get(v___x_2612_, 3);
v_diag_2616_ = lean_ctor_get(v___x_2612_, 4);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; 
v_unused_2627_ = lean_ctor_get(v___x_2612_, 2);
lean_dec(v_unused_2627_);
v___x_2618_ = v___x_2612_;
v_isShared_2619_ = v_isSharedCheck_2626_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_diag_2616_);
lean_inc(v_postponed_2615_);
lean_inc(v_cache_2614_);
lean_inc(v_mctx_2613_);
lean_dec(v___x_2612_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2626_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2620_ = lean_box(0);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 2, v_zetaDeltaFVarIds_2609_);
v___x_2622_ = v___x_2618_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_mctx_2613_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_cache_2614_);
lean_ctor_set(v_reuseFailAlloc_2625_, 2, v_zetaDeltaFVarIds_2609_);
lean_ctor_set(v_reuseFailAlloc_2625_, 3, v_postponed_2615_);
lean_ctor_set(v_reuseFailAlloc_2625_, 4, v_diag_2616_);
v___x_2622_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_st_ref_put(v_a_2608_, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2620_);
return v___x_2624_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2608_ = stack[0].m_obj;
lean_object* v_zetaDeltaFVarIds_2609_ = stack[1].m_obj;
lean_object* v_a_x3f_2610_ = stack[2].m_obj;
lean_object* v_res_2628_;
v_res_2628_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2608_, v_zetaDeltaFVarIds_2609_, v_a_x3f_2610_);
stack->m_obj
 = v_res_2628_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object* v_a_2629_, lean_object* v_zetaDeltaFVarIds_2630_, lean_object* v_a_x3f_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2629_, v_zetaDeltaFVarIds_2630_, v_a_x3f_2631_);
lean_dec(v_a_x3f_2631_);
lean_dec(v_a_2629_);
return v_res_2633_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0(void){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2634_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
return v___x_2636_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_2638_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
lean_ctor_set(v___x_2638_, 2, v___x_2637_);
lean_ctor_set(v___x_2638_, 3, v___x_2637_);
lean_ctor_set(v___x_2638_, 4, v___x_2637_);
lean_ctor_set(v___x_2638_, 5, v___x_2637_);
return v___x_2638_;
}
}
lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* v_type_2639_, lean_object* v_value_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v_cache_2650_; lean_object* v_a_2652_; lean_object* v___x_2663_; lean_object* v_mctx_2664_; lean_object* v_zetaDeltaFVarIds_2665_; lean_object* v_postponed_2666_; lean_object* v_diag_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2733_; 
v___x_2648_ = lean_box(1);
v___x_2649_ = lean_st_ref_get(v_a_2644_);
v_cache_2650_ = lean_ctor_get(v___x_2649_, 1);
lean_inc_ref(v_cache_2650_);
lean_dec(v___x_2649_);
v___x_2663_ = lean_st_ref_take(v_a_2644_);
v_mctx_2664_ = lean_ctor_get(v___x_2663_, 0);
v_zetaDeltaFVarIds_2665_ = lean_ctor_get(v___x_2663_, 2);
v_postponed_2666_ = lean_ctor_get(v___x_2663_, 3);
v_diag_2667_ = lean_ctor_get(v___x_2663_, 4);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; 
v_unused_2734_ = lean_ctor_get(v___x_2663_, 1);
lean_dec(v_unused_2734_);
v___x_2669_ = v___x_2663_;
v_isShared_2670_ = v_isSharedCheck_2733_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_diag_2667_);
lean_inc(v_postponed_2666_);
lean_inc(v_zetaDeltaFVarIds_2665_);
lean_inc(v_mctx_2664_);
lean_dec(v___x_2663_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2733_;
goto v_resetjp_2668_;
}
v___jp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
v___x_2653_ = lean_box(0);
v___x_2654_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2644_, v_cache_2650_, v___x_2653_);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2661_ == 0)
{
lean_object* v_unused_2662_; 
v_unused_2662_ = lean_ctor_get(v___x_2654_, 0);
lean_dec(v_unused_2662_);
v___x_2656_ = v___x_2654_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_dec(v___x_2654_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
lean_ctor_set_tag(v___x_2656_, 1);
lean_ctor_set(v___x_2656_, 0, v_a_2652_);
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2652_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2671_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 1, v___x_2671_);
v___x_2673_ = v___x_2669_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_mctx_2664_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2732_, 2, v_zetaDeltaFVarIds_2665_);
lean_ctor_set(v_reuseFailAlloc_2732_, 3, v_postponed_2666_);
lean_ctor_set(v_reuseFailAlloc_2732_, 4, v_diag_2667_);
v___x_2673_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; lean_object* v_keyedConfig_2675_; lean_object* v_zetaDeltaSet_2676_; lean_object* v_lctx_2677_; lean_object* v_localInstances_2678_; lean_object* v_defEqCtx_x3f_2679_; lean_object* v_synthPendingDepth_2680_; lean_object* v_customCanUnfoldPredicate_x3f_2681_; uint8_t v_univApprox_2682_; uint8_t v_inTypeClassResolution_2683_; uint8_t v_cacheInferType_2684_; uint8_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v_mctx_2688_; lean_object* v_cache_2689_; lean_object* v_zetaDeltaFVarIds_2690_; lean_object* v_postponed_2691_; lean_object* v_diag_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2731_; 
v___x_2674_ = lean_st_ref_put(v_a_2644_, v___x_2673_);
v_keyedConfig_2675_ = lean_ctor_get(v_a_2643_, 0);
v_zetaDeltaSet_2676_ = lean_ctor_get(v_a_2643_, 1);
v_lctx_2677_ = lean_ctor_get(v_a_2643_, 2);
v_localInstances_2678_ = lean_ctor_get(v_a_2643_, 3);
v_defEqCtx_x3f_2679_ = lean_ctor_get(v_a_2643_, 4);
v_synthPendingDepth_2680_ = lean_ctor_get(v_a_2643_, 5);
v_customCanUnfoldPredicate_x3f_2681_ = lean_ctor_get(v_a_2643_, 6);
v_univApprox_2682_ = lean_ctor_get_uint8(v_a_2643_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2683_ = lean_ctor_get_uint8(v_a_2643_, sizeof(void*)*7 + 2);
v_cacheInferType_2684_ = lean_ctor_get_uint8(v_a_2643_, sizeof(void*)*7 + 3);
v___x_2685_ = 1;
lean_inc(v_customCanUnfoldPredicate_x3f_2681_);
lean_inc(v_synthPendingDepth_2680_);
lean_inc(v_defEqCtx_x3f_2679_);
lean_inc_ref(v_localInstances_2678_);
lean_inc_ref(v_lctx_2677_);
lean_inc(v_zetaDeltaSet_2676_);
lean_inc_ref(v_keyedConfig_2675_);
v___x_2686_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2686_, 0, v_keyedConfig_2675_);
lean_ctor_set(v___x_2686_, 1, v_zetaDeltaSet_2676_);
lean_ctor_set(v___x_2686_, 2, v_lctx_2677_);
lean_ctor_set(v___x_2686_, 3, v_localInstances_2678_);
lean_ctor_set(v___x_2686_, 4, v_defEqCtx_x3f_2679_);
lean_ctor_set(v___x_2686_, 5, v_synthPendingDepth_2680_);
lean_ctor_set(v___x_2686_, 6, v_customCanUnfoldPredicate_x3f_2681_);
lean_ctor_set_uint8(v___x_2686_, sizeof(void*)*7, v___x_2685_);
lean_ctor_set_uint8(v___x_2686_, sizeof(void*)*7 + 1, v_univApprox_2682_);
lean_ctor_set_uint8(v___x_2686_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2683_);
lean_ctor_set_uint8(v___x_2686_, sizeof(void*)*7 + 3, v_cacheInferType_2684_);
v___x_2687_ = lean_st_ref_take(v_a_2644_);
v_mctx_2688_ = lean_ctor_get(v___x_2687_, 0);
v_cache_2689_ = lean_ctor_get(v___x_2687_, 1);
v_zetaDeltaFVarIds_2690_ = lean_ctor_get(v___x_2687_, 2);
v_postponed_2691_ = lean_ctor_get(v___x_2687_, 3);
v_diag_2692_ = lean_ctor_get(v___x_2687_, 4);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2694_ = v___x_2687_;
v_isShared_2695_ = v_isSharedCheck_2731_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_diag_2692_);
lean_inc(v_postponed_2691_);
lean_inc(v_zetaDeltaFVarIds_2690_);
lean_inc(v_cache_2689_);
lean_inc(v_mctx_2688_);
lean_dec(v___x_2687_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2731_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v_a_2697_; lean_object* v___x_2701_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 2, v___x_2648_);
v___x_2701_ = v___x_2694_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_mctx_2688_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_cache_2689_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v_postponed_2691_);
lean_ctor_set(v_reuseFailAlloc_2730_, 4, v_diag_2692_);
v___x_2701_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2700_;
}
v___jp_2696_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_box(0);
v___x_2699_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2644_, v_zetaDeltaFVarIds_2690_, v___x_2698_);
lean_dec_ref(v___x_2699_);
v_a_2652_ = v_a_2697_;
goto v___jp_2651_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_st_ref_put(v_a_2644_, v___x_2701_);
v___x_2703_ = l_Lean_Meta_Closure_collectExpr(v_type_2639_, v_a_2641_, v_a_2642_, v___x_2686_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2705_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
v___x_2705_ = l_Lean_Meta_Closure_collectExpr(v_value_2640_, v_a_2641_, v_a_2642_, v___x_2686_, v_a_2644_, v_a_2645_, v_a_2646_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2707_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v___x_2707_ = l_Lean_Meta_Closure_process(v_a_2641_, v_a_2642_, v___x_2686_, v_a_2644_, v_a_2645_, v_a_2646_);
lean_dec_ref_known(v___x_2686_, 7);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2725_; 
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v___x_2707_, 0);
lean_dec(v_unused_2726_);
v___x_2709_ = v___x_2707_;
v_isShared_2710_ = v_isSharedCheck_2725_;
goto v_resetjp_2708_;
}
else
{
lean_dec(v___x_2707_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2725_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2711_; lean_object* v___x_2713_; 
v___x_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2711_, 0, v_a_2704_);
lean_ctor_set(v___x_2711_, 1, v_a_2706_);
lean_inc_ref(v___x_2711_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set_tag(v___x_2709_, 1);
lean_ctor_set(v___x_2709_, 0, v___x_2711_);
v___x_2713_ = v___x_2709_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
v___x_2714_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2644_, v_zetaDeltaFVarIds_2690_, v___x_2713_);
lean_dec_ref(v___x_2714_);
v___x_2715_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2644_, v_cache_2650_, v___x_2713_);
lean_dec_ref(v___x_2713_);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2722_ == 0)
{
lean_object* v_unused_2723_; 
v_unused_2723_ = lean_ctor_get(v___x_2715_, 0);
lean_dec(v_unused_2723_);
v___x_2717_ = v___x_2715_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_dec(v___x_2715_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2711_);
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2711_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
else
{
lean_object* v_a_2727_; 
lean_dec(v_a_2706_);
lean_dec(v_a_2704_);
v_a_2727_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2707_, 1);
v_a_2697_ = v_a_2727_;
goto v___jp_2696_;
}
}
else
{
lean_object* v_a_2728_; 
lean_dec(v_a_2704_);
lean_dec_ref_known(v___x_2686_, 7);
v_a_2728_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___x_2705_, 1);
v_a_2697_ = v_a_2728_;
goto v___jp_2696_;
}
}
else
{
lean_object* v_a_2729_; 
lean_dec_ref_known(v___x_2686_, 7);
lean_dec_ref(v_value_2640_);
v_a_2729_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2703_, 1);
v_a_2697_ = v_a_2729_;
goto v___jp_2696_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Closure_mkValueTypeClosureAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2639_ = stack[0].m_obj;
lean_object* v_value_2640_ = stack[1].m_obj;
lean_object* v_a_2641_ = stack[2].m_obj;
lean_object* v_a_2642_ = stack[3].m_obj;
lean_object* v_a_2643_ = stack[4].m_obj;
lean_object* v_a_2644_ = stack[5].m_obj;
lean_object* v_a_2645_ = stack[6].m_obj;
lean_object* v_a_2646_ = stack[7].m_obj;
lean_object* v_res_2735_;
v_res_2735_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_2639_, v_value_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
stack->m_obj
 = v_res_2735_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* v_type_2736_, lean_object* v_value_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_2736_, v_value_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec(v_a_2739_);
lean_dec_ref(v_a_2738_);
return v_res_2745_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_instMonadEIO___redArg();
return v___x_2746_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object* v_msg_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v_toApplicative_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2797_; 
v___x_2754_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0);
v___x_2755_ = l_StateRefT_x27_instMonad___redArg(v___x_2754_);
v_toApplicative_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2797_ == 0)
{
lean_object* v_unused_2798_; 
v_unused_2798_ = lean_ctor_get(v___x_2755_, 1);
lean_dec(v_unused_2798_);
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2797_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_toApplicative_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2797_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v_toFunctor_2760_; lean_object* v_toSeq_2761_; lean_object* v_toSeqLeft_2762_; lean_object* v_toSeqRight_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2795_; 
v_toFunctor_2760_ = lean_ctor_get(v_toApplicative_2756_, 0);
v_toSeq_2761_ = lean_ctor_get(v_toApplicative_2756_, 2);
v_toSeqLeft_2762_ = lean_ctor_get(v_toApplicative_2756_, 3);
v_toSeqRight_2763_ = lean_ctor_get(v_toApplicative_2756_, 4);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_toApplicative_2756_);
if (v_isSharedCheck_2795_ == 0)
{
lean_object* v_unused_2796_; 
v_unused_2796_ = lean_ctor_get(v_toApplicative_2756_, 1);
lean_dec(v_unused_2796_);
v___x_2765_ = v_toApplicative_2756_;
v_isShared_2766_ = v_isSharedCheck_2795_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_toSeqRight_2763_);
lean_inc(v_toSeqLeft_2762_);
lean_inc(v_toSeq_2761_);
lean_inc(v_toFunctor_2760_);
lean_dec(v_toApplicative_2756_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2795_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___f_2767_; lean_object* v___f_2768_; lean_object* v___f_2769_; lean_object* v___f_2770_; lean_object* v___x_2771_; lean_object* v___f_2772_; lean_object* v___f_2773_; lean_object* v___f_2774_; lean_object* v___x_2776_; 
v___f_2767_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1));
v___f_2768_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2));
lean_inc_ref(v_toFunctor_2760_);
v___f_2769_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2769_, 0, v_toFunctor_2760_);
v___f_2770_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2770_, 0, v_toFunctor_2760_);
v___x_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___f_2769_);
lean_ctor_set(v___x_2771_, 1, v___f_2770_);
v___f_2772_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2772_, 0, v_toSeqRight_2763_);
v___f_2773_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2773_, 0, v_toSeqLeft_2762_);
v___f_2774_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2774_, 0, v_toSeq_2761_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 4, v___f_2772_);
lean_ctor_set(v___x_2765_, 3, v___f_2773_);
lean_ctor_set(v___x_2765_, 2, v___f_2774_);
lean_ctor_set(v___x_2765_, 1, v___f_2767_);
lean_ctor_set(v___x_2765_, 0, v___x_2771_);
v___x_2776_ = v___x_2765_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v___f_2767_);
lean_ctor_set(v_reuseFailAlloc_2794_, 2, v___f_2774_);
lean_ctor_set(v_reuseFailAlloc_2794_, 3, v___f_2773_);
lean_ctor_set(v_reuseFailAlloc_2794_, 4, v___f_2772_);
v___x_2776_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2778_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___f_2768_);
lean_ctor_set(v___x_2758_, 0, v___x_2776_);
v___x_2778_ = v___x_2758_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v___f_2768_);
v___x_2778_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___f_2779_; lean_object* v___f_2780_; lean_object* v___f_2781_; lean_object* v___f_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_12362__overap_2791_; lean_object* v___x_2792_; 
lean_inc_ref_n(v___x_2778_, 6);
v___f_2779_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2779_, 0, v___x_2778_);
v___f_2780_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2780_, 0, v___x_2778_);
v___f_2781_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2781_, 0, v___x_2778_);
v___f_2782_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2782_, 0, v___x_2778_);
v___x_2783_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2783_, 0, lean_box(0));
lean_closure_set(v___x_2783_, 1, lean_box(0));
lean_closure_set(v___x_2783_, 2, v___x_2778_);
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
lean_ctor_set(v___x_2784_, 1, v___f_2779_);
v___x_2785_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2785_, 0, lean_box(0));
lean_closure_set(v___x_2785_, 1, lean_box(0));
lean_closure_set(v___x_2785_, 2, v___x_2778_);
v___x_2786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2784_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
lean_ctor_set(v___x_2786_, 2, v___f_2780_);
lean_ctor_set(v___x_2786_, 3, v___f_2781_);
lean_ctor_set(v___x_2786_, 4, v___f_2782_);
v___x_2787_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2787_, 0, lean_box(0));
lean_closure_set(v___x_2787_, 1, lean_box(0));
lean_closure_set(v___x_2787_, 2, v___x_2778_);
v___x_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2786_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
v___x_2789_ = lean_box(0);
v___x_2790_ = l_instInhabitedOfMonad___redArg(v___x_2788_, v___x_2789_);
v___x_12362__overap_2791_ = lean_panic_fn_borrowed(v___x_2790_, v_msg_2749_);
lean_dec(v___x_2790_);
lean_inc(v___y_2752_);
lean_inc_ref(v___y_2751_);
v___x_2792_ = lean_apply_4(v___x_12362__overap_2791_, v___y_2750_, v___y_2751_, v___y_2752_, lean_box(0));
return v___x_2792_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2749_ = stack[0].m_obj;
lean_object* v___y_2750_ = stack[1].m_obj;
lean_object* v___y_2751_ = stack[2].m_obj;
lean_object* v___y_2752_ = stack[3].m_obj;
lean_object* v_res_2799_;
v_res_2799_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_msg_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
stack->m_obj
 = v_res_2799_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object* v_msg_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_msg_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
return v_res_2805_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(lean_object* v_a_2806_, lean_object* v_x_2807_){
_start:
{
if (lean_obj_tag(v_x_2807_) == 0)
{
uint8_t v___x_2808_; 
v___x_2808_ = 0;
return v___x_2808_;
}
else
{
lean_object* v_key_2809_; lean_object* v_tail_2810_; uint8_t v___x_2811_; 
v_key_2809_ = lean_ctor_get(v_x_2807_, 0);
v_tail_2810_ = lean_ctor_get(v_x_2807_, 2);
v___x_2811_ = l_Lean_instBEqFVarId_beq(v_key_2809_, v_a_2806_);
if (v___x_2811_ == 0)
{
v_x_2807_ = v_tail_2810_;
goto _start;
}
else
{
return v___x_2811_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2806_ = stack[0].m_obj;
lean_object* v_x_2807_ = stack[1].m_obj;
uint8_t v_res_2813_;
v_res_2813_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2806_, v_x_2807_);
stack->m_num = v_res_2813_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg___boxed(lean_object* v_a_2814_, lean_object* v_x_2815_){
_start:
{
uint8_t v_res_2816_; lean_object* v_r_2817_; 
v_res_2816_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2814_, v_x_2815_);
lean_dec(v_x_2815_);
lean_dec(v_a_2814_);
v_r_2817_ = lean_box(v_res_2816_);
return v_r_2817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(lean_object* v_x_2818_, lean_object* v_x_2819_){
_start:
{
if (lean_obj_tag(v_x_2819_) == 0)
{
return v_x_2818_;
}
else
{
lean_object* v_key_2820_; lean_object* v_value_2821_; lean_object* v_tail_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2845_; 
v_key_2820_ = lean_ctor_get(v_x_2819_, 0);
v_value_2821_ = lean_ctor_get(v_x_2819_, 1);
v_tail_2822_ = lean_ctor_get(v_x_2819_, 2);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_x_2819_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2824_ = v_x_2819_;
v_isShared_2825_ = v_isSharedCheck_2845_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_tail_2822_);
lean_inc(v_value_2821_);
lean_inc(v_key_2820_);
lean_dec(v_x_2819_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2845_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2826_; uint64_t v___x_2827_; uint64_t v___x_2828_; uint64_t v___x_2829_; uint64_t v_fold_2830_; uint64_t v___x_2831_; uint64_t v___x_2832_; uint64_t v___x_2833_; size_t v___x_2834_; size_t v___x_2835_; size_t v___x_2836_; size_t v___x_2837_; size_t v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2826_ = lean_array_get_size(v_x_2818_);
v___x_2827_ = l_Lean_instHashableFVarId_hash(v_key_2820_);
v___x_2828_ = 32ULL;
v___x_2829_ = lean_uint64_shift_right(v___x_2827_, v___x_2828_);
v_fold_2830_ = lean_uint64_xor(v___x_2827_, v___x_2829_);
v___x_2831_ = 16ULL;
v___x_2832_ = lean_uint64_shift_right(v_fold_2830_, v___x_2831_);
v___x_2833_ = lean_uint64_xor(v_fold_2830_, v___x_2832_);
v___x_2834_ = lean_uint64_to_usize(v___x_2833_);
v___x_2835_ = lean_usize_of_nat(v___x_2826_);
v___x_2836_ = ((size_t)1ULL);
v___x_2837_ = lean_usize_sub(v___x_2835_, v___x_2836_);
v___x_2838_ = lean_usize_land(v___x_2834_, v___x_2837_);
v___x_2839_ = lean_array_uget_borrowed(v_x_2818_, v___x_2838_);
lean_inc(v___x_2839_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 2, v___x_2839_);
v___x_2841_ = v___x_2824_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_key_2820_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_value_2821_);
lean_ctor_set(v_reuseFailAlloc_2844_, 2, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_array_uset(v_x_2818_, v___x_2838_, v___x_2841_);
v_x_2818_ = v___x_2842_;
v_x_2819_ = v_tail_2822_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(lean_object* v_i_2846_, lean_object* v_source_2847_, lean_object* v_target_2848_){
_start:
{
lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = lean_array_get_size(v_source_2847_);
v___x_2850_ = lean_nat_dec_lt(v_i_2846_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_dec_ref(v_source_2847_);
lean_dec(v_i_2846_);
return v_target_2848_;
}
else
{
lean_object* v_es_2851_; lean_object* v___x_2852_; lean_object* v_source_2853_; lean_object* v_target_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v_es_2851_ = lean_array_fget(v_source_2847_, v_i_2846_);
v___x_2852_ = lean_box(0);
v_source_2853_ = lean_array_fset(v_source_2847_, v_i_2846_, v___x_2852_);
v_target_2854_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_target_2848_, v_es_2851_);
v___x_2855_ = lean_unsigned_to_nat(1u);
v___x_2856_ = lean_nat_add(v_i_2846_, v___x_2855_);
lean_dec(v_i_2846_);
v_i_2846_ = v___x_2856_;
v_source_2847_ = v_source_2853_;
v_target_2848_ = v_target_2854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(lean_object* v_data_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v_nbuckets_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2859_ = lean_array_get_size(v_data_2858_);
v___x_2860_ = lean_unsigned_to_nat(2u);
v_nbuckets_2861_ = lean_nat_mul(v___x_2859_, v___x_2860_);
v___x_2862_ = lean_unsigned_to_nat(0u);
v___x_2863_ = lean_box(0);
v___x_2864_ = lean_mk_array(v_nbuckets_2861_, v___x_2863_);
v___x_2865_ = lean_array_propagate_mark(v_data_2858_, v___x_2864_);
v___x_2866_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v___x_2862_, v_data_2858_, v___x_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(lean_object* v_m_2867_, lean_object* v_a_2868_, lean_object* v_b_2869_){
_start:
{
lean_object* v_size_2870_; lean_object* v_buckets_2871_; lean_object* v___x_2872_; uint64_t v___x_2873_; uint64_t v___x_2874_; uint64_t v___x_2875_; uint64_t v_fold_2876_; uint64_t v___x_2877_; uint64_t v___x_2878_; uint64_t v___x_2879_; size_t v___x_2880_; size_t v___x_2881_; size_t v___x_2882_; size_t v___x_2883_; size_t v___x_2884_; lean_object* v_bkt_2885_; uint8_t v___x_2886_; 
v_size_2870_ = lean_ctor_get(v_m_2867_, 0);
v_buckets_2871_ = lean_ctor_get(v_m_2867_, 1);
v___x_2872_ = lean_array_get_size(v_buckets_2871_);
v___x_2873_ = l_Lean_instHashableFVarId_hash(v_a_2868_);
v___x_2874_ = 32ULL;
v___x_2875_ = lean_uint64_shift_right(v___x_2873_, v___x_2874_);
v_fold_2876_ = lean_uint64_xor(v___x_2873_, v___x_2875_);
v___x_2877_ = 16ULL;
v___x_2878_ = lean_uint64_shift_right(v_fold_2876_, v___x_2877_);
v___x_2879_ = lean_uint64_xor(v_fold_2876_, v___x_2878_);
v___x_2880_ = lean_uint64_to_usize(v___x_2879_);
v___x_2881_ = lean_usize_of_nat(v___x_2872_);
v___x_2882_ = ((size_t)1ULL);
v___x_2883_ = lean_usize_sub(v___x_2881_, v___x_2882_);
v___x_2884_ = lean_usize_land(v___x_2880_, v___x_2883_);
v_bkt_2885_ = lean_array_uget_borrowed(v_buckets_2871_, v___x_2884_);
v___x_2886_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2868_, v_bkt_2885_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2907_; 
lean_inc_ref(v_buckets_2871_);
lean_inc(v_size_2870_);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_m_2867_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; lean_object* v_unused_2909_; 
v_unused_2908_ = lean_ctor_get(v_m_2867_, 1);
lean_dec(v_unused_2908_);
v_unused_2909_ = lean_ctor_get(v_m_2867_, 0);
lean_dec(v_unused_2909_);
v___x_2888_ = v_m_2867_;
v_isShared_2889_ = v_isSharedCheck_2907_;
goto v_resetjp_2887_;
}
else
{
lean_dec(v_m_2867_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2907_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v_size_x27_2891_; lean_object* v___x_2892_; lean_object* v_buckets_x27_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v___x_2890_ = lean_unsigned_to_nat(1u);
v_size_x27_2891_ = lean_nat_add(v_size_2870_, v___x_2890_);
lean_dec(v_size_2870_);
lean_inc(v_bkt_2885_);
v___x_2892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2892_, 0, v_a_2868_);
lean_ctor_set(v___x_2892_, 1, v_b_2869_);
lean_ctor_set(v___x_2892_, 2, v_bkt_2885_);
v_buckets_x27_2893_ = lean_array_uset(v_buckets_2871_, v___x_2884_, v___x_2892_);
v___x_2894_ = lean_unsigned_to_nat(4u);
v___x_2895_ = lean_nat_mul(v_size_x27_2891_, v___x_2894_);
v___x_2896_ = lean_unsigned_to_nat(3u);
v___x_2897_ = lean_nat_div(v___x_2895_, v___x_2896_);
lean_dec(v___x_2895_);
v___x_2898_ = lean_array_get_size(v_buckets_x27_2893_);
v___x_2899_ = lean_nat_dec_le(v___x_2897_, v___x_2898_);
lean_dec(v___x_2897_);
if (v___x_2899_ == 0)
{
lean_object* v_val_2900_; lean_object* v___x_2902_; 
v_val_2900_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_2893_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 1, v_val_2900_);
lean_ctor_set(v___x_2888_, 0, v_size_x27_2891_);
v___x_2902_ = v___x_2888_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_size_x27_2891_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_val_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
else
{
lean_object* v___x_2905_; 
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 1, v_buckets_x27_2893_);
lean_ctor_set(v___x_2888_, 0, v_size_x27_2891_);
v___x_2905_ = v___x_2888_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_size_x27_2891_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_buckets_x27_2893_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_dec(v_b_2869_);
lean_dec(v_a_2868_);
return v_m_2867_;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object* v_m_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v_buckets_2912_; lean_object* v___x_2913_; uint64_t v___x_2914_; uint64_t v___x_2915_; uint64_t v___x_2916_; uint64_t v_fold_2917_; uint64_t v___x_2918_; uint64_t v___x_2919_; uint64_t v___x_2920_; size_t v___x_2921_; size_t v___x_2922_; size_t v___x_2923_; size_t v___x_2924_; size_t v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v_buckets_2912_ = lean_ctor_get(v_m_2910_, 1);
v___x_2913_ = lean_array_get_size(v_buckets_2912_);
v___x_2914_ = l_Lean_instHashableFVarId_hash(v_a_2911_);
v___x_2915_ = 32ULL;
v___x_2916_ = lean_uint64_shift_right(v___x_2914_, v___x_2915_);
v_fold_2917_ = lean_uint64_xor(v___x_2914_, v___x_2916_);
v___x_2918_ = 16ULL;
v___x_2919_ = lean_uint64_shift_right(v_fold_2917_, v___x_2918_);
v___x_2920_ = lean_uint64_xor(v_fold_2917_, v___x_2919_);
v___x_2921_ = lean_uint64_to_usize(v___x_2920_);
v___x_2922_ = lean_usize_of_nat(v___x_2913_);
v___x_2923_ = ((size_t)1ULL);
v___x_2924_ = lean_usize_sub(v___x_2922_, v___x_2923_);
v___x_2925_ = lean_usize_land(v___x_2921_, v___x_2924_);
v___x_2926_ = lean_array_uget_borrowed(v_buckets_2912_, v___x_2925_);
v___x_2927_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2911_, v___x_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2910_ = stack[0].m_obj;
lean_object* v_a_2911_ = stack[1].m_obj;
uint8_t v_res_2928_;
v_res_2928_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_2910_, v_a_2911_);
stack->m_num = v_res_2928_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object* v_m_2929_, lean_object* v_a_2930_){
_start:
{
uint8_t v_res_2931_; lean_object* v_r_2932_; 
v_res_2931_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_2929_, v_a_2930_);
lean_dec(v_a_2930_);
lean_dec_ref(v_m_2929_);
v_r_2932_ = lean_box(v_res_2931_);
return v_r_2932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(lean_object* v_a_2933_, lean_object* v_x_2934_){
_start:
{
if (lean_obj_tag(v_x_2934_) == 0)
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_box(0);
return v___x_2935_;
}
else
{
lean_object* v_key_2936_; lean_object* v_value_2937_; lean_object* v_tail_2938_; uint8_t v___x_2939_; 
v_key_2936_ = lean_ctor_get(v_x_2934_, 0);
v_value_2937_ = lean_ctor_get(v_x_2934_, 1);
v_tail_2938_ = lean_ctor_get(v_x_2934_, 2);
v___x_2939_ = lean_expr_eqv(v_key_2936_, v_a_2933_);
if (v___x_2939_ == 0)
{
v_x_2934_ = v_tail_2938_;
goto _start;
}
else
{
lean_object* v___x_2941_; 
lean_inc(v_value_2937_);
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_value_2937_);
return v___x_2941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_a_2942_, lean_object* v_x_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2942_, v_x_2943_);
lean_dec(v_x_2943_);
lean_dec_ref(v_a_2942_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(lean_object* v_m_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v_buckets_2947_; lean_object* v___x_2948_; uint64_t v___x_2949_; uint64_t v___x_2950_; uint64_t v___x_2951_; uint64_t v_fold_2952_; uint64_t v___x_2953_; uint64_t v___x_2954_; uint64_t v___x_2955_; size_t v___x_2956_; size_t v___x_2957_; size_t v___x_2958_; size_t v___x_2959_; size_t v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_buckets_2947_ = lean_ctor_get(v_m_2945_, 1);
v___x_2948_ = lean_array_get_size(v_buckets_2947_);
v___x_2949_ = l_Lean_Expr_hash(v_a_2946_);
v___x_2950_ = 32ULL;
v___x_2951_ = lean_uint64_shift_right(v___x_2949_, v___x_2950_);
v_fold_2952_ = lean_uint64_xor(v___x_2949_, v___x_2951_);
v___x_2953_ = 16ULL;
v___x_2954_ = lean_uint64_shift_right(v_fold_2952_, v___x_2953_);
v___x_2955_ = lean_uint64_xor(v_fold_2952_, v___x_2954_);
v___x_2956_ = lean_uint64_to_usize(v___x_2955_);
v___x_2957_ = lean_usize_of_nat(v___x_2948_);
v___x_2958_ = ((size_t)1ULL);
v___x_2959_ = lean_usize_sub(v___x_2957_, v___x_2958_);
v___x_2960_ = lean_usize_land(v___x_2956_, v___x_2959_);
v___x_2961_ = lean_array_uget_borrowed(v_buckets_2947_, v___x_2960_);
v___x_2962_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2946_, v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg___boxed(lean_object* v_m_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_2963_, v_a_2964_);
lean_dec_ref(v_a_2964_);
lean_dec_ref(v_m_2963_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(lean_object* v_a_2966_, lean_object* v_b_2967_, lean_object* v_x_2968_){
_start:
{
if (lean_obj_tag(v_x_2968_) == 0)
{
lean_dec(v_b_2967_);
lean_dec_ref(v_a_2966_);
return v_x_2968_;
}
else
{
lean_object* v_key_2969_; lean_object* v_value_2970_; lean_object* v_tail_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2983_; 
v_key_2969_ = lean_ctor_get(v_x_2968_, 0);
v_value_2970_ = lean_ctor_get(v_x_2968_, 1);
v_tail_2971_ = lean_ctor_get(v_x_2968_, 2);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_x_2968_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2973_ = v_x_2968_;
v_isShared_2974_ = v_isSharedCheck_2983_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_tail_2971_);
lean_inc(v_value_2970_);
lean_inc(v_key_2969_);
lean_dec(v_x_2968_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2983_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
uint8_t v___x_2975_; 
v___x_2975_ = lean_expr_eqv(v_key_2969_, v_a_2966_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_2966_, v_b_2967_, v_tail_2971_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 2, v___x_2976_);
v___x_2978_ = v___x_2973_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_key_2969_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v_value_2970_);
lean_ctor_set(v_reuseFailAlloc_2979_, 2, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
else
{
lean_object* v___x_2981_; 
lean_dec(v_value_2970_);
lean_dec(v_key_2969_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 1, v_b_2967_);
lean_ctor_set(v___x_2973_, 0, v_a_2966_);
v___x_2981_ = v___x_2973_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2966_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_b_2967_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_tail_2971_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(lean_object* v_x_2984_, lean_object* v_x_2985_){
_start:
{
if (lean_obj_tag(v_x_2985_) == 0)
{
return v_x_2984_;
}
else
{
lean_object* v_key_2986_; lean_object* v_value_2987_; lean_object* v_tail_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3011_; 
v_key_2986_ = lean_ctor_get(v_x_2985_, 0);
v_value_2987_ = lean_ctor_get(v_x_2985_, 1);
v_tail_2988_ = lean_ctor_get(v_x_2985_, 2);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_x_2985_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_2990_ = v_x_2985_;
v_isShared_2991_ = v_isSharedCheck_3011_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_tail_2988_);
lean_inc(v_value_2987_);
lean_inc(v_key_2986_);
lean_dec(v_x_2985_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3011_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2992_; uint64_t v___x_2993_; uint64_t v___x_2994_; uint64_t v___x_2995_; uint64_t v_fold_2996_; uint64_t v___x_2997_; uint64_t v___x_2998_; uint64_t v___x_2999_; size_t v___x_3000_; size_t v___x_3001_; size_t v___x_3002_; size_t v___x_3003_; size_t v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_2992_ = lean_array_get_size(v_x_2984_);
v___x_2993_ = l_Lean_Expr_hash(v_key_2986_);
v___x_2994_ = 32ULL;
v___x_2995_ = lean_uint64_shift_right(v___x_2993_, v___x_2994_);
v_fold_2996_ = lean_uint64_xor(v___x_2993_, v___x_2995_);
v___x_2997_ = 16ULL;
v___x_2998_ = lean_uint64_shift_right(v_fold_2996_, v___x_2997_);
v___x_2999_ = lean_uint64_xor(v_fold_2996_, v___x_2998_);
v___x_3000_ = lean_uint64_to_usize(v___x_2999_);
v___x_3001_ = lean_usize_of_nat(v___x_2992_);
v___x_3002_ = ((size_t)1ULL);
v___x_3003_ = lean_usize_sub(v___x_3001_, v___x_3002_);
v___x_3004_ = lean_usize_land(v___x_3000_, v___x_3003_);
v___x_3005_ = lean_array_uget_borrowed(v_x_2984_, v___x_3004_);
lean_inc(v___x_3005_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 2, v___x_3005_);
v___x_3007_ = v___x_2990_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_key_2986_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_value_2987_);
lean_ctor_set(v_reuseFailAlloc_3010_, 2, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_array_uset(v_x_2984_, v___x_3004_, v___x_3007_);
v_x_2984_ = v___x_3008_;
v_x_2985_ = v_tail_2988_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(lean_object* v_i_3012_, lean_object* v_source_3013_, lean_object* v_target_3014_){
_start:
{
lean_object* v___x_3015_; uint8_t v___x_3016_; 
v___x_3015_ = lean_array_get_size(v_source_3013_);
v___x_3016_ = lean_nat_dec_lt(v_i_3012_, v___x_3015_);
if (v___x_3016_ == 0)
{
lean_dec_ref(v_source_3013_);
lean_dec(v_i_3012_);
return v_target_3014_;
}
else
{
lean_object* v_es_3017_; lean_object* v___x_3018_; lean_object* v_source_3019_; lean_object* v_target_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_es_3017_ = lean_array_fget(v_source_3013_, v_i_3012_);
v___x_3018_ = lean_box(0);
v_source_3019_ = lean_array_fset(v_source_3013_, v_i_3012_, v___x_3018_);
v_target_3020_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_target_3014_, v_es_3017_);
v___x_3021_ = lean_unsigned_to_nat(1u);
v___x_3022_ = lean_nat_add(v_i_3012_, v___x_3021_);
lean_dec(v_i_3012_);
v_i_3012_ = v___x_3022_;
v_source_3013_ = v_source_3019_;
v_target_3014_ = v_target_3020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(lean_object* v_data_3024_){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v_nbuckets_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3025_ = lean_array_get_size(v_data_3024_);
v___x_3026_ = lean_unsigned_to_nat(2u);
v_nbuckets_3027_ = lean_nat_mul(v___x_3025_, v___x_3026_);
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = lean_box(0);
v___x_3030_ = lean_mk_array(v_nbuckets_3027_, v___x_3029_);
v___x_3031_ = lean_array_propagate_mark(v_data_3024_, v___x_3030_);
v___x_3032_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v___x_3028_, v_data_3024_, v___x_3031_);
return v___x_3032_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(lean_object* v_a_3033_, lean_object* v_x_3034_){
_start:
{
if (lean_obj_tag(v_x_3034_) == 0)
{
uint8_t v___x_3035_; 
v___x_3035_ = 0;
return v___x_3035_;
}
else
{
lean_object* v_key_3036_; lean_object* v_tail_3037_; uint8_t v___x_3038_; 
v_key_3036_ = lean_ctor_get(v_x_3034_, 0);
v_tail_3037_ = lean_ctor_get(v_x_3034_, 2);
v___x_3038_ = lean_expr_eqv(v_key_3036_, v_a_3033_);
if (v___x_3038_ == 0)
{
v_x_3034_ = v_tail_3037_;
goto _start;
}
else
{
return v___x_3038_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3033_ = stack[0].m_obj;
lean_object* v_x_3034_ = stack[1].m_obj;
uint8_t v_res_3040_;
v_res_3040_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3033_, v_x_3034_);
stack->m_num = v_res_3040_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_3041_, lean_object* v_x_3042_){
_start:
{
uint8_t v_res_3043_; lean_object* v_r_3044_; 
v_res_3043_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3041_, v_x_3042_);
lean_dec(v_x_3042_);
lean_dec_ref(v_a_3041_);
v_r_3044_ = lean_box(v_res_3043_);
return v_r_3044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(lean_object* v_m_3045_, lean_object* v_a_3046_, lean_object* v_b_3047_){
_start:
{
lean_object* v_size_3048_; lean_object* v_buckets_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3092_; 
v_size_3048_ = lean_ctor_get(v_m_3045_, 0);
v_buckets_3049_ = lean_ctor_get(v_m_3045_, 1);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_m_3045_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3051_ = v_m_3045_;
v_isShared_3052_ = v_isSharedCheck_3092_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_buckets_3049_);
lean_inc(v_size_3048_);
lean_dec(v_m_3045_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3092_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; uint64_t v___x_3054_; uint64_t v___x_3055_; uint64_t v___x_3056_; uint64_t v_fold_3057_; uint64_t v___x_3058_; uint64_t v___x_3059_; uint64_t v___x_3060_; size_t v___x_3061_; size_t v___x_3062_; size_t v___x_3063_; size_t v___x_3064_; size_t v___x_3065_; lean_object* v_bkt_3066_; uint8_t v___x_3067_; 
v___x_3053_ = lean_array_get_size(v_buckets_3049_);
v___x_3054_ = l_Lean_Expr_hash(v_a_3046_);
v___x_3055_ = 32ULL;
v___x_3056_ = lean_uint64_shift_right(v___x_3054_, v___x_3055_);
v_fold_3057_ = lean_uint64_xor(v___x_3054_, v___x_3056_);
v___x_3058_ = 16ULL;
v___x_3059_ = lean_uint64_shift_right(v_fold_3057_, v___x_3058_);
v___x_3060_ = lean_uint64_xor(v_fold_3057_, v___x_3059_);
v___x_3061_ = lean_uint64_to_usize(v___x_3060_);
v___x_3062_ = lean_usize_of_nat(v___x_3053_);
v___x_3063_ = ((size_t)1ULL);
v___x_3064_ = lean_usize_sub(v___x_3062_, v___x_3063_);
v___x_3065_ = lean_usize_land(v___x_3061_, v___x_3064_);
v_bkt_3066_ = lean_array_uget_borrowed(v_buckets_3049_, v___x_3065_);
v___x_3067_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3046_, v_bkt_3066_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; lean_object* v_size_x27_3069_; lean_object* v___x_3070_; lean_object* v_buckets_x27_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
v___x_3068_ = lean_unsigned_to_nat(1u);
v_size_x27_3069_ = lean_nat_add(v_size_3048_, v___x_3068_);
lean_dec(v_size_3048_);
lean_inc(v_bkt_3066_);
v___x_3070_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3070_, 0, v_a_3046_);
lean_ctor_set(v___x_3070_, 1, v_b_3047_);
lean_ctor_set(v___x_3070_, 2, v_bkt_3066_);
v_buckets_x27_3071_ = lean_array_uset(v_buckets_3049_, v___x_3065_, v___x_3070_);
v___x_3072_ = lean_unsigned_to_nat(4u);
v___x_3073_ = lean_nat_mul(v_size_x27_3069_, v___x_3072_);
v___x_3074_ = lean_unsigned_to_nat(3u);
v___x_3075_ = lean_nat_div(v___x_3073_, v___x_3074_);
lean_dec(v___x_3073_);
v___x_3076_ = lean_array_get_size(v_buckets_x27_3071_);
v___x_3077_ = lean_nat_dec_le(v___x_3075_, v___x_3076_);
lean_dec(v___x_3075_);
if (v___x_3077_ == 0)
{
lean_object* v_val_3078_; lean_object* v___x_3080_; 
v_val_3078_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_buckets_x27_3071_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 1, v_val_3078_);
lean_ctor_set(v___x_3051_, 0, v_size_x27_3069_);
v___x_3080_ = v___x_3051_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_size_x27_3069_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v_val_3078_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
else
{
lean_object* v___x_3083_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 1, v_buckets_x27_3071_);
lean_ctor_set(v___x_3051_, 0, v_size_x27_3069_);
v___x_3083_ = v___x_3051_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_size_x27_3069_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_buckets_x27_3071_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
else
{
lean_object* v___x_3085_; lean_object* v_buckets_x27_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3090_; 
lean_inc(v_bkt_3066_);
v___x_3085_ = lean_box(0);
v_buckets_x27_3086_ = lean_array_uset(v_buckets_3049_, v___x_3065_, v___x_3085_);
v___x_3087_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3046_, v_b_3047_, v_bkt_3066_);
v___x_3088_ = lean_array_uset(v_buckets_x27_3086_, v___x_3065_, v___x_3087_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 1, v___x_3088_);
v___x_3090_ = v___x_3051_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_size_3048_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v___x_3088_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
}
lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object* v_g_3093_, lean_object* v_e_3094_, lean_object* v_a_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_a_3101_; lean_object* v_fst_3102_; lean_object* v___y_3108_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = lean_st_ref_get(v_a_3095_);
v___x_3112_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v___x_3111_, v_e_3094_);
lean_dec(v___x_3111_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v___x_3113_; 
lean_inc_ref(v_g_3093_);
lean_inc(v___y_3098_);
lean_inc_ref(v___y_3097_);
lean_inc_ref(v_e_3094_);
v___x_3113_ = lean_apply_5(v_g_3093_, v_e_3094_, v___y_3096_, v___y_3097_, v___y_3098_, lean_box(0));
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v_fst_3115_; lean_object* v_snd_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3161_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
v_fst_3115_ = lean_ctor_get(v_a_3114_, 0);
v_snd_3116_ = lean_ctor_get(v_a_3114_, 1);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_a_3114_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3118_ = v_a_3114_;
v_isShared_3119_ = v_isSharedCheck_3161_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_snd_3116_);
lean_inc(v_fst_3115_);
lean_dec(v_a_3114_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3161_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v_d_3121_; lean_object* v_b_3122_; lean_object* v___y_3123_; uint8_t v___x_3128_; 
v___x_3128_ = lean_unbox(v_fst_3115_);
lean_dec(v_fst_3115_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3131_; 
lean_dec_ref(v_g_3093_);
v___x_3129_ = lean_box(0);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3129_);
v___x_3131_ = v___x_3118_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3129_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_snd_3116_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
v_a_3101_ = v___x_3131_;
v_fst_3102_ = v___x_3129_;
goto v___jp_3100_;
}
}
else
{
switch(lean_obj_tag(v_e_3094_))
{
case 7:
{
lean_object* v_binderType_3133_; lean_object* v_body_3134_; 
lean_del_object(v___x_3118_);
v_binderType_3133_ = lean_ctor_get(v_e_3094_, 1);
v_body_3134_ = lean_ctor_get(v_e_3094_, 2);
lean_inc_ref(v_body_3134_);
lean_inc_ref(v_binderType_3133_);
v_d_3121_ = v_binderType_3133_;
v_b_3122_ = v_body_3134_;
v___y_3123_ = v_a_3095_;
goto v___jp_3120_;
}
case 6:
{
lean_object* v_binderType_3135_; lean_object* v_body_3136_; 
lean_del_object(v___x_3118_);
v_binderType_3135_ = lean_ctor_get(v_e_3094_, 1);
v_body_3136_ = lean_ctor_get(v_e_3094_, 2);
lean_inc_ref(v_body_3136_);
lean_inc_ref(v_binderType_3135_);
v_d_3121_ = v_binderType_3135_;
v_b_3122_ = v_body_3136_;
v___y_3123_ = v_a_3095_;
goto v___jp_3120_;
}
case 8:
{
lean_object* v_type_3137_; lean_object* v_value_3138_; lean_object* v_body_3139_; lean_object* v___x_3140_; 
lean_del_object(v___x_3118_);
v_type_3137_ = lean_ctor_get(v_e_3094_, 1);
v_value_3138_ = lean_ctor_get(v_e_3094_, 2);
v_body_3139_ = lean_ctor_get(v_e_3094_, 3);
lean_inc_ref(v_type_3137_);
lean_inc_ref(v_g_3093_);
v___x_3140_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3093_, v_type_3137_, v_a_3095_, v_snd_3116_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v_snd_3142_; lean_object* v___x_3143_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
v_snd_3142_ = lean_ctor_get(v_a_3141_, 1);
lean_inc(v_snd_3142_);
lean_dec(v_a_3141_);
lean_inc_ref(v_value_3138_);
lean_inc_ref(v_g_3093_);
v___x_3143_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3093_, v_value_3138_, v_a_3095_, v_snd_3142_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v_snd_3145_; lean_object* v___x_3146_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref_known(v___x_3143_, 1);
v_snd_3145_ = lean_ctor_get(v_a_3144_, 1);
lean_inc(v_snd_3145_);
lean_dec(v_a_3144_);
lean_inc_ref(v_body_3139_);
v___x_3146_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3093_, v_body_3139_, v_a_3095_, v_snd_3145_, v___y_3097_, v___y_3098_);
v___y_3108_ = v___x_3146_;
goto v___jp_3107_;
}
else
{
lean_dec_ref(v_g_3093_);
v___y_3108_ = v___x_3143_;
goto v___jp_3107_;
}
}
else
{
lean_dec_ref(v_g_3093_);
v___y_3108_ = v___x_3140_;
goto v___jp_3107_;
}
}
case 5:
{
lean_object* v_fn_3147_; lean_object* v_arg_3148_; lean_object* v___x_3149_; 
lean_del_object(v___x_3118_);
v_fn_3147_ = lean_ctor_get(v_e_3094_, 0);
v_arg_3148_ = lean_ctor_get(v_e_3094_, 1);
lean_inc_ref(v_fn_3147_);
lean_inc_ref(v_g_3093_);
v___x_3149_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3093_, v_fn_3147_, v_a_3095_, v_snd_3116_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; lean_object* v_snd_3151_; lean_object* v___x_3152_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc(v_a_3150_);
lean_dec_ref_known(v___x_3149_, 1);
v_snd_3151_ = lean_ctor_get(v_a_3150_, 1);
lean_inc(v_snd_3151_);
lean_dec(v_a_3150_);
lean_inc_ref(v_arg_3148_);
v___x_3152_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3093_, v_arg_3148_, v_a_3095_, v_snd_3151_, v___y_3097_, v___y_3098_);
v___y_3108_ = v___x_3152_;
goto v___jp_3107_;
}
else
{
lean_dec_ref(v_g_3093_);
v___y_3108_ = v___x_3149_;
goto v___jp_3107_;
}
}
case 10:
{
lean_object* v_expr_3153_; lean_object* v___x_3154_; 
lean_del_object(v___x_3118_);
v_expr_3153_ = lean_ctor_get(v_e_3094_, 1);
lean_inc_ref(v_expr_3153_);
v___x_3154_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3093_, v_expr_3153_, v_a_3095_, v_snd_3116_, v___y_3097_, v___y_3098_);
v___y_3108_ = v___x_3154_;
goto v___jp_3107_;
}
case 11:
{
lean_object* v_struct_3155_; lean_object* v___x_3156_; 
lean_del_object(v___x_3118_);
v_struct_3155_ = lean_ctor_get(v_e_3094_, 2);
lean_inc_ref(v_struct_3155_);
v___x_3156_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3093_, v_struct_3155_, v_a_3095_, v_snd_3116_, v___y_3097_, v___y_3098_);
v___y_3108_ = v___x_3156_;
goto v___jp_3107_;
}
default: 
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
lean_dec_ref(v_g_3093_);
v___x_3157_ = lean_box(0);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3157_);
v___x_3159_ = v___x_3118_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_snd_3116_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
v_a_3101_ = v___x_3159_;
v_fst_3102_ = v___x_3157_;
goto v___jp_3100_;
}
}
}
}
v___jp_3120_:
{
lean_object* v___x_3124_; 
lean_inc_ref(v_g_3093_);
v___x_3124_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3093_, v_d_3121_, v___y_3123_, v_snd_3116_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_a_3125_; lean_object* v_snd_3126_; lean_object* v___x_3127_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3125_);
lean_dec_ref_known(v___x_3124_, 1);
v_snd_3126_ = lean_ctor_get(v_a_3125_, 1);
lean_inc(v_snd_3126_);
lean_dec(v_a_3125_);
v___x_3127_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3093_, v_b_3122_, v___y_3123_, v_snd_3126_, v___y_3097_, v___y_3098_);
v___y_3108_ = v___x_3127_;
goto v___jp_3107_;
}
else
{
lean_dec_ref(v_b_3122_);
lean_dec_ref(v_g_3093_);
v___y_3108_ = v___x_3124_;
goto v___jp_3107_;
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec_ref(v_e_3094_);
lean_dec_ref(v_g_3093_);
v_a_3162_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3113_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3113_);
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
else
{
lean_object* v_val_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3178_; 
lean_dec_ref(v_e_3094_);
lean_dec_ref(v_g_3093_);
v_val_3170_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3172_ = v___x_3112_;
v_isShared_3173_ = v_isSharedCheck_3178_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_val_3170_);
lean_dec(v___x_3112_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3178_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3174_, 0, v_val_3170_);
lean_ctor_set(v___x_3174_, 1, v___y_3096_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set_tag(v___x_3172_, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3174_);
v___x_3176_ = v___x_3172_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
v___jp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3103_ = lean_st_ref_take(v_a_3095_);
v___x_3104_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v___x_3103_, v_e_3094_, v_fst_3102_);
v___x_3105_ = lean_st_ref_put(v_a_3095_, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3106_, 0, v_a_3101_);
return v___x_3106_;
}
v___jp_3107_:
{
if (lean_obj_tag(v___y_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v_fst_3110_; 
v_a_3109_ = lean_ctor_get(v___y_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___y_3108_, 1);
v_fst_3110_ = lean_ctor_get(v_a_3109_, 0);
lean_inc(v_fst_3110_);
v_a_3101_ = v_a_3109_;
v_fst_3102_ = v_fst_3110_;
goto v___jp_3100_;
}
else
{
lean_dec_ref(v_e_3094_);
return v___y_3108_;
}
}
}
}
LEAN_EXPORT void l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_3093_ = stack[0].m_obj;
lean_object* v_e_3094_ = stack[1].m_obj;
lean_object* v_a_3095_ = stack[2].m_obj;
lean_object* v___y_3096_ = stack[3].m_obj;
lean_object* v___y_3097_ = stack[4].m_obj;
lean_object* v___y_3098_ = stack[5].m_obj;
lean_object* v_res_3179_;
v_res_3179_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3093_, v_e_3094_, v_a_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
stack->m_obj
 = v_res_3179_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___boxed(lean_object* v_g_3180_, lean_object* v_e_3181_, lean_object* v_a_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3180_, v_e_3181_, v_a_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v_a_3182_);
return v_res_3187_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
return v___x_3189_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3190_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3191_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
lean_ctor_set(v___x_3193_, 2, v___x_3192_);
lean_ctor_set(v___x_3193_, 3, v___x_3192_);
lean_ctor_set(v___x_3193_, 4, v___x_3191_);
lean_ctor_set(v___x_3193_, 5, v___x_3191_);
lean_ctor_set(v___x_3193_, 6, v___x_3191_);
lean_ctor_set(v___x_3193_, 7, v___x_3191_);
lean_ctor_set(v___x_3193_, 8, v___x_3191_);
lean_ctor_set(v___x_3193_, 9, v___x_3191_);
lean_ctor_set(v___x_3193_, 10, v___x_3191_);
lean_ctor_set(v___x_3193_, 11, v___x_3190_);
return v___x_3193_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = lean_unsigned_to_nat(32u);
v___x_3195_ = lean_mk_empty_array_with_capacity(v___x_3194_);
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
return v___x_3196_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3(void){
_start:
{
size_t v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3197_ = ((size_t)5ULL);
v___x_3198_ = lean_unsigned_to_nat(0u);
v___x_3199_ = lean_unsigned_to_nat(32u);
v___x_3200_ = lean_mk_empty_array_with_capacity(v___x_3199_);
v___x_3201_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2);
v___x_3202_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
lean_ctor_set(v___x_3202_, 1, v___x_3200_);
lean_ctor_set(v___x_3202_, 2, v___x_3198_);
lean_ctor_set(v___x_3202_, 3, v___x_3198_);
lean_ctor_set_usize(v___x_3202_, 4, v___x_3197_);
return v___x_3202_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3203_ = lean_box(1);
v___x_3204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3);
v___x_3205_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v___x_3204_);
lean_ctor_set(v___x_3206_, 2, v___x_3203_);
return v___x_3206_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(lean_object* v_msgData_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v___x_3211_; lean_object* v_toCold_3212_; lean_object* v_env_3213_; lean_object* v_options_3214_; uint8_t v___x_3215_; lean_object* v_env_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3211_ = lean_st_ref_get(v___y_3209_);
v_toCold_3212_ = lean_ctor_get(v___y_3208_, 0);
v_env_3213_ = lean_ctor_get(v___x_3211_, 0);
lean_inc_ref(v_env_3213_);
lean_dec(v___x_3211_);
v_options_3214_ = lean_ctor_get(v_toCold_3212_, 2);
v___x_3215_ = 0;
v_env_3216_ = l_Lean_Environment_setRecordingDeps(v_env_3213_, v___x_3215_);
v___x_3217_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3218_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4);
lean_inc_ref(v_options_3214_);
v___x_3219_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3219_, 0, v_env_3216_);
lean_ctor_set(v___x_3219_, 1, v___x_3217_);
lean_ctor_set(v___x_3219_, 2, v___x_3218_);
lean_ctor_set(v___x_3219_, 3, v_options_3214_);
v___x_3220_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
lean_ctor_set(v___x_3220_, 1, v_msgData_3207_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3207_ = stack[0].m_obj;
lean_object* v___y_3208_ = stack[1].m_obj;
lean_object* v___y_3209_ = stack[2].m_obj;
lean_object* v_res_3222_;
v_res_3222_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msgData_3207_, v___y_3208_, v___y_3209_);
stack->m_obj
 = v_res_3222_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___boxed(lean_object* v_msgData_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msgData_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
return v_res_3227_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(lean_object* v_msg_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v_ref_3232_; lean_object* v___x_3233_; lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3242_; 
v_ref_3232_ = lean_ctor_get(v___y_3229_, 2);
v___x_3233_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3228_, v___y_3229_, v___y_3230_);
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3236_ = v___x_3233_;
v_isShared_3237_ = v_isSharedCheck_3242_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3233_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3242_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; lean_object* v___x_3240_; 
lean_inc(v_ref_3232_);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v_ref_3232_);
lean_ctor_set(v___x_3238_, 1, v_a_3234_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set_tag(v___x_3236_, 1);
lean_ctor_set(v___x_3236_, 0, v___x_3238_);
v___x_3240_ = v___x_3236_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3228_ = stack[0].m_obj;
lean_object* v___y_3229_ = stack[1].m_obj;
lean_object* v___y_3230_ = stack[2].m_obj;
lean_object* v_res_3243_;
v_res_3243_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3228_, v___y_3229_, v___y_3230_);
stack->m_obj
 = v_res_3243_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg___boxed(lean_object* v_msg_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
return v_res_3248_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3249_; double v___x_3250_; 
v___x_3249_ = lean_unsigned_to_nat(0u);
v___x_3250_ = lean_float_of_nat(v___x_3249_);
return v___x_3250_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object* v_cls_3254_, lean_object* v_msg_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v_ref_3260_; lean_object* v___x_3261_; lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3308_; 
v_ref_3260_ = lean_ctor_get(v___y_3257_, 2);
v___x_3261_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3255_, v___y_3257_, v___y_3258_);
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3264_ = v___x_3261_;
v_isShared_3265_ = v_isSharedCheck_3308_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3261_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3308_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v_traceState_3267_; lean_object* v_env_3268_; lean_object* v_nextMacroScope_3269_; lean_object* v_ngen_3270_; lean_object* v_auxDeclNGen_3271_; lean_object* v_cache_3272_; lean_object* v_recordedDeps_3273_; lean_object* v_messages_3274_; lean_object* v_infoState_3275_; lean_object* v_snapshotTasks_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3307_; 
v___x_3266_ = lean_st_ref_take(v___y_3258_);
v_traceState_3267_ = lean_ctor_get(v___x_3266_, 4);
v_env_3268_ = lean_ctor_get(v___x_3266_, 0);
v_nextMacroScope_3269_ = lean_ctor_get(v___x_3266_, 1);
v_ngen_3270_ = lean_ctor_get(v___x_3266_, 2);
v_auxDeclNGen_3271_ = lean_ctor_get(v___x_3266_, 3);
v_cache_3272_ = lean_ctor_get(v___x_3266_, 5);
v_recordedDeps_3273_ = lean_ctor_get(v___x_3266_, 6);
v_messages_3274_ = lean_ctor_get(v___x_3266_, 7);
v_infoState_3275_ = lean_ctor_get(v___x_3266_, 8);
v_snapshotTasks_3276_ = lean_ctor_get(v___x_3266_, 9);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3278_ = v___x_3266_;
v_isShared_3279_ = v_isSharedCheck_3307_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_snapshotTasks_3276_);
lean_inc(v_infoState_3275_);
lean_inc(v_messages_3274_);
lean_inc(v_recordedDeps_3273_);
lean_inc(v_cache_3272_);
lean_inc(v_traceState_3267_);
lean_inc(v_auxDeclNGen_3271_);
lean_inc(v_ngen_3270_);
lean_inc(v_nextMacroScope_3269_);
lean_inc(v_env_3268_);
lean_dec(v___x_3266_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3307_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
uint64_t v_tid_3280_; lean_object* v_traces_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3306_; 
v_tid_3280_ = lean_ctor_get_uint64(v_traceState_3267_, sizeof(void*)*1);
v_traces_3281_ = lean_ctor_get(v_traceState_3267_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v_traceState_3267_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3283_ = v_traceState_3267_;
v_isShared_3284_ = v_isSharedCheck_3306_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_traces_3281_);
lean_dec(v_traceState_3267_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3306_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; double v___x_3287_; uint8_t v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3285_ = lean_box(0);
v___x_3286_ = lean_box(0);
v___x_3287_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3288_ = 0;
v___x_3289_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3290_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3290_, 0, v_cls_3254_);
lean_ctor_set(v___x_3290_, 1, v___x_3286_);
lean_ctor_set(v___x_3290_, 2, v___x_3289_);
lean_ctor_set_float(v___x_3290_, sizeof(void*)*3, v___x_3287_);
lean_ctor_set_float(v___x_3290_, sizeof(void*)*3 + 8, v___x_3287_);
lean_ctor_set_uint8(v___x_3290_, sizeof(void*)*3 + 16, v___x_3288_);
v___x_3291_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3292_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v_a_3262_);
lean_ctor_set(v___x_3292_, 2, v___x_3291_);
lean_inc(v_ref_3260_);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v_ref_3260_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = l_Lean_PersistentArray_push___redArg(v_traces_3281_, v___x_3293_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v___x_3294_);
v___x_3296_ = v___x_3283_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3294_);
lean_ctor_set_uint64(v_reuseFailAlloc_3305_, sizeof(void*)*1, v_tid_3280_);
v___x_3296_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3298_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 4, v___x_3296_);
v___x_3298_ = v___x_3278_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_env_3268_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_nextMacroScope_3269_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_ngen_3270_);
lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_auxDeclNGen_3271_);
lean_ctor_set(v_reuseFailAlloc_3304_, 4, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3304_, 5, v_cache_3272_);
lean_ctor_set(v_reuseFailAlloc_3304_, 6, v_recordedDeps_3273_);
lean_ctor_set(v_reuseFailAlloc_3304_, 7, v_messages_3274_);
lean_ctor_set(v_reuseFailAlloc_3304_, 8, v_infoState_3275_);
lean_ctor_set(v_reuseFailAlloc_3304_, 9, v_snapshotTasks_3276_);
v___x_3298_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3299_ = lean_st_ref_put(v___y_3258_, v___x_3298_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3285_);
lean_ctor_set(v___x_3300_, 1, v___y_3256_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 0, v___x_3300_);
v___x_3302_ = v___x_3264_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3254_ = stack[0].m_obj;
lean_object* v_msg_3255_ = stack[1].m_obj;
lean_object* v___y_3256_ = stack[2].m_obj;
lean_object* v___y_3257_ = stack[3].m_obj;
lean_object* v___y_3258_ = stack[4].m_obj;
lean_object* v_res_3309_;
v_res_3309_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3254_, v_msg_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
stack->m_obj
 = v_res_3309_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(lean_object* v_cls_3310_, lean_object* v_msg_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3310_, v_msg_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object* v_a_3317_, lean_object* v_x_3318_){
_start:
{
if (lean_obj_tag(v_x_3318_) == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_box(0);
return v___x_3319_;
}
else
{
lean_object* v_key_3320_; lean_object* v_value_3321_; lean_object* v_tail_3322_; uint8_t v___x_3323_; 
v_key_3320_ = lean_ctor_get(v_x_3318_, 0);
v_value_3321_ = lean_ctor_get(v_x_3318_, 1);
v_tail_3322_ = lean_ctor_get(v_x_3318_, 2);
v___x_3323_ = l_Lean_instBEqFVarId_beq(v_key_3320_, v_a_3317_);
if (v___x_3323_ == 0)
{
v_x_3318_ = v_tail_3322_;
goto _start;
}
else
{
lean_object* v___x_3325_; 
lean_inc(v_value_3321_);
v___x_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3325_, 0, v_value_3321_);
return v___x_3325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_3326_, lean_object* v_x_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3326_, v_x_3327_);
lean_dec(v_x_3327_);
lean_dec(v_a_3326_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object* v_m_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v_buckets_3331_; lean_object* v___x_3332_; uint64_t v___x_3333_; uint64_t v___x_3334_; uint64_t v___x_3335_; uint64_t v_fold_3336_; uint64_t v___x_3337_; uint64_t v___x_3338_; uint64_t v___x_3339_; size_t v___x_3340_; size_t v___x_3341_; size_t v___x_3342_; size_t v___x_3343_; size_t v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v_buckets_3331_ = lean_ctor_get(v_m_3329_, 1);
v___x_3332_ = lean_array_get_size(v_buckets_3331_);
v___x_3333_ = l_Lean_instHashableFVarId_hash(v_a_3330_);
v___x_3334_ = 32ULL;
v___x_3335_ = lean_uint64_shift_right(v___x_3333_, v___x_3334_);
v_fold_3336_ = lean_uint64_xor(v___x_3333_, v___x_3335_);
v___x_3337_ = 16ULL;
v___x_3338_ = lean_uint64_shift_right(v_fold_3336_, v___x_3337_);
v___x_3339_ = lean_uint64_xor(v_fold_3336_, v___x_3338_);
v___x_3340_ = lean_uint64_to_usize(v___x_3339_);
v___x_3341_ = lean_usize_of_nat(v___x_3332_);
v___x_3342_ = ((size_t)1ULL);
v___x_3343_ = lean_usize_sub(v___x_3341_, v___x_3342_);
v___x_3344_ = lean_usize_land(v___x_3340_, v___x_3343_);
v___x_3345_ = lean_array_uget_borrowed(v_buckets_3331_, v___x_3344_);
v___x_3346_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3330_, v___x_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object* v_m_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3347_, v_a_3348_);
lean_dec(v_a_3348_);
lean_dec_ref(v_m_3347_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object* v___x_3350_, lean_object* v_m_3351_, lean_object* v_e_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
uint8_t v___x_18102__boxed_3357_; lean_object* v_res_3358_; 
v___x_18102__boxed_3357_ = lean_unbox(v___x_3350_);
v_res_3358_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(v___x_18102__boxed_3357_, v_m_3351_, v_e_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec_ref(v_e_3352_);
return v_res_3358_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0(void){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_unsigned_to_nat(16u);
v___x_3361_ = lean_mk_array(v___x_3360_, v___x_3359_);
return v___x_3361_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1(void){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3362_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0);
v___x_3363_ = lean_unsigned_to_nat(0u);
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v___x_3362_);
return v___x_3364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5(void){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3368_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4));
v___x_3369_ = lean_unsigned_to_nat(4u);
v___x_3370_ = lean_unsigned_to_nat(390u);
v___x_3371_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3));
v___x_3372_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3373_ = l_mkPanicMessageWithDecl(v___x_3372_, v___x_3371_, v___x_3370_, v___x_3369_, v___x_3368_);
return v___x_3373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6));
v___x_3376_ = l_Lean_stringToMessageData(v___x_3375_);
return v___x_3376_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3385_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3386_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12));
v___x_3387_ = l_Lean_Name_append(v___x_3386_, v___x_3385_);
return v___x_3387_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14));
v___x_3390_ = l_Lean_stringToMessageData(v___x_3389_);
return v___x_3390_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16));
v___x_3393_ = l_Lean_stringToMessageData(v___x_3392_);
return v___x_3393_;
}
}
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(lean_object* v_m_3394_, lean_object* v_fvarId_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3394_, v_fvarId_3395_);
if (lean_obj_tag(v___x_3400_) == 1)
{
lean_object* v_val_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3515_; 
v_val_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3515_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_val_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3515_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v_fst_3405_; lean_object* v_snd_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3514_; 
v_fst_3405_ = lean_ctor_get(v_val_3401_, 0);
v_snd_3406_ = lean_ctor_get(v_val_3401_, 1);
v_isSharedCheck_3514_ = !lean_is_exclusive(v_val_3401_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3408_ = v_val_3401_;
v_isShared_3409_ = v_isSharedCheck_3514_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_snd_3406_);
lean_inc(v_fst_3405_);
lean_dec(v_val_3401_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3514_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v_tempMark_3410_; lean_object* v_doneMark_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; 
v_tempMark_3410_ = lean_ctor_get(v_a_3396_, 0);
v_doneMark_3411_ = lean_ctor_get(v_a_3396_, 1);
v___x_3412_ = l_Lean_LocalDecl_fvarId(v_fst_3405_);
v___x_3413_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_doneMark_3411_, v___x_3412_);
if (v___x_3413_ == 0)
{
lean_object* v_toCold_3414_; lean_object* v_options_3415_; lean_object* v_inheritedTraceOptions_3416_; uint8_t v_hasTrace_3417_; uint8_t v___x_3418_; lean_object* v___x_3419_; lean_object* v___f_3420_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3482_; lean_object* v_tempMark_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; 
lean_del_object(v___x_3408_);
lean_del_object(v___x_3403_);
v_toCold_3414_ = lean_ctor_get(v_a_3397_, 0);
v_options_3415_ = lean_ctor_get(v_toCold_3414_, 2);
v_inheritedTraceOptions_3416_ = lean_ctor_get(v_toCold_3414_, 11);
v_hasTrace_3417_ = lean_ctor_get_uint8(v_options_3415_, sizeof(void*)*1);
v___x_3418_ = 1;
v___x_3419_ = lean_box(v___x_3418_);
v___f_3420_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3420_, 0, v___x_3419_);
lean_closure_set(v___f_3420_, 1, v_m_3394_);
if (v_hasTrace_3417_ == 0)
{
lean_inc_ref(v_tempMark_3410_);
v___y_3482_ = v_a_3396_;
v_tempMark_3483_ = v_tempMark_3410_;
v___y_3484_ = v_a_3397_;
v___y_3485_ = v_a_3398_;
goto v___jp_3481_;
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; 
v___x_3491_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3492_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_3493_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3416_, v_options_3415_, v___x_3492_);
if (v___x_3493_ == 0)
{
lean_inc_ref(v_tempMark_3410_);
v___y_3482_ = v_a_3396_;
v_tempMark_3483_ = v_tempMark_3410_;
v___y_3484_ = v_a_3397_;
v___y_3485_ = v_a_3398_;
goto v___jp_3481_;
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3494_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15);
lean_inc(v___x_3412_);
v___x_3495_ = l_Lean_mkFVar(v___x_3412_);
v___x_3496_ = l_Lean_MessageData_ofExpr(v___x_3495_);
v___x_3497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3494_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17);
v___x_3499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3497_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = l_Lean_LocalDecl_type(v_fst_3405_);
v___x_3501_ = l_Lean_MessageData_ofExpr(v___x_3500_);
v___x_3502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3499_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v___x_3491_, v___x_3502_, v_a_3396_, v_a_3397_, v_a_3398_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v_snd_3505_; lean_object* v_tempMark_3506_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v_snd_3505_ = lean_ctor_get(v_a_3504_, 1);
lean_inc(v_snd_3505_);
lean_dec(v_a_3504_);
v_tempMark_3506_ = lean_ctor_get(v_snd_3505_, 0);
lean_inc_ref(v_tempMark_3506_);
v___y_3482_ = v_snd_3505_;
v_tempMark_3483_ = v_tempMark_3506_;
v___y_3484_ = v_a_3397_;
v___y_3485_ = v_a_3398_;
goto v___jp_3481_;
}
else
{
lean_dec_ref(v___f_3420_);
lean_dec(v___x_3412_);
lean_dec(v_snd_3406_);
lean_dec(v_fst_3405_);
return v___x_3503_;
}
}
}
v___jp_3421_:
{
lean_object* v_tempMark_3425_; lean_object* v_doneMark_3426_; lean_object* v_newDecls_3427_; lean_object* v_newArgs_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3473_; 
v_tempMark_3425_ = lean_ctor_get(v___y_3424_, 0);
v_doneMark_3426_ = lean_ctor_get(v___y_3424_, 1);
v_newDecls_3427_ = lean_ctor_get(v___y_3424_, 2);
v_newArgs_3428_ = lean_ctor_get(v___y_3424_, 3);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___y_3424_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3430_ = v___y_3424_;
v_isShared_3431_ = v_isSharedCheck_3473_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_newArgs_3428_);
lean_inc(v_newDecls_3427_);
lean_inc(v_doneMark_3426_);
lean_inc(v_tempMark_3425_);
lean_dec(v___y_3424_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3473_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
v___x_3432_ = lean_box(0);
lean_inc(v___x_3412_);
v___x_3433_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_tempMark_3425_, v___x_3412_, v___x_3432_);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3433_);
v___x_3435_ = v___x_3430_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_doneMark_3426_);
lean_ctor_set(v_reuseFailAlloc_3472_, 2, v_newDecls_3427_);
lean_ctor_set(v_reuseFailAlloc_3472_, 3, v_newArgs_3428_);
v___x_3435_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3436_ = l_Lean_LocalDecl_type(v_fst_3405_);
v___x_3437_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1);
v___x_3438_ = lean_st_mk_ref(v___x_3437_);
v___x_3439_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v___f_3420_, v___x_3436_, v___x_3438_, v___x_3435_, v___y_3423_, v___y_3422_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3471_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3471_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3471_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v_snd_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3469_; 
v_snd_3444_ = lean_ctor_get(v_a_3440_, 1);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_a_3440_);
if (v_isSharedCheck_3469_ == 0)
{
lean_object* v_unused_3470_; 
v_unused_3470_ = lean_ctor_get(v_a_3440_, 0);
lean_dec(v_unused_3470_);
v___x_3446_ = v_a_3440_;
v_isShared_3447_ = v_isSharedCheck_3469_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_snd_3444_);
lean_dec(v_a_3440_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3469_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3448_; lean_object* v_tempMark_3449_; lean_object* v_doneMark_3450_; lean_object* v_newDecls_3451_; lean_object* v_newArgs_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3468_; 
v___x_3448_ = lean_st_ref_get(v___x_3438_);
lean_dec(v___x_3438_);
lean_dec(v___x_3448_);
v_tempMark_3449_ = lean_ctor_get(v_snd_3444_, 0);
v_doneMark_3450_ = lean_ctor_get(v_snd_3444_, 1);
v_newDecls_3451_ = lean_ctor_get(v_snd_3444_, 2);
v_newArgs_3452_ = lean_ctor_get(v_snd_3444_, 3);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_snd_3444_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3454_ = v_snd_3444_;
v_isShared_3455_ = v_isSharedCheck_3468_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_newArgs_3452_);
lean_inc(v_newDecls_3451_);
lean_inc(v_doneMark_3450_);
lean_inc(v_tempMark_3449_);
lean_dec(v_snd_3444_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3468_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3456_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_doneMark_3450_, v___x_3412_, v___x_3432_);
v___x_3457_ = lean_array_push(v_newDecls_3451_, v_fst_3405_);
v___x_3458_ = lean_array_push(v_newArgs_3452_, v_snd_3406_);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 3, v___x_3458_);
lean_ctor_set(v___x_3454_, 2, v___x_3457_);
lean_ctor_set(v___x_3454_, 1, v___x_3456_);
v___x_3460_ = v___x_3454_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_tempMark_3449_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3467_, 2, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3467_, 3, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3462_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v___x_3460_);
lean_ctor_set(v___x_3446_, 0, v___x_3432_);
v___x_3462_ = v___x_3446_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3432_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3464_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3462_);
v___x_3464_ = v___x_3442_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3438_);
lean_dec(v___x_3412_);
lean_dec(v_snd_3406_);
lean_dec(v_fst_3405_);
return v___x_3439_;
}
}
}
}
v___jp_3474_:
{
uint8_t v___x_3478_; 
v___x_3478_ = l_Lean_LocalDecl_isLet(v_fst_3405_, v___x_3418_);
if (v___x_3478_ == 0)
{
v___y_3422_ = v___y_3477_;
v___y_3423_ = v___y_3476_;
v___y_3424_ = v___y_3475_;
goto v___jp_3421_;
}
else
{
if (v___x_3413_ == 0)
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
lean_dec_ref(v___f_3420_);
lean_dec(v___x_3412_);
lean_dec(v_snd_3406_);
lean_dec(v_fst_3405_);
v___x_3479_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5);
v___x_3480_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v___x_3479_, v___y_3475_, v___y_3476_, v___y_3477_);
return v___x_3480_;
}
else
{
v___y_3422_ = v___y_3477_;
v___y_3423_ = v___y_3476_;
v___y_3424_ = v___y_3475_;
goto v___jp_3421_;
}
}
}
v___jp_3481_:
{
uint8_t v___x_3486_; 
v___x_3486_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_tempMark_3483_, v___x_3412_);
lean_dec_ref(v_tempMark_3483_);
if (v___x_3486_ == 0)
{
v___y_3475_ = v___y_3482_;
v___y_3476_ = v___y_3484_;
v___y_3477_ = v___y_3485_;
goto v___jp_3474_;
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec_ref(v___y_3482_);
v___x_3487_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7);
v___x_3488_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v___x_3487_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v_snd_3490_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v_snd_3490_ = lean_ctor_get(v_a_3489_, 1);
lean_inc(v_snd_3490_);
lean_dec(v_a_3489_);
v___y_3475_ = v_snd_3490_;
v___y_3476_ = v___y_3484_;
v___y_3477_ = v___y_3485_;
goto v___jp_3474_;
}
else
{
lean_dec_ref(v___f_3420_);
lean_dec(v___x_3412_);
lean_dec(v_snd_3406_);
lean_dec(v_fst_3405_);
return v___x_3488_;
}
}
}
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3509_; 
lean_dec(v___x_3412_);
lean_dec(v_snd_3406_);
lean_dec(v_fst_3405_);
lean_dec_ref(v_m_3394_);
v___x_3507_ = lean_box(0);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 1, v_a_3396_);
lean_ctor_set(v___x_3408_, 0, v___x_3507_);
v___x_3509_ = v___x_3408_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3507_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_a_3396_);
v___x_3509_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
lean_object* v___x_3511_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set_tag(v___x_3403_, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3509_);
v___x_3511_ = v___x_3403_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
}
}
else
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
lean_dec(v___x_3400_);
lean_dec_ref(v_m_3394_);
v___x_3516_ = lean_box(0);
v___x_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
lean_ctor_set(v___x_3517_, 1, v_a_3396_);
v___x_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
return v___x_3518_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_3394_ = stack[0].m_obj;
lean_object* v_fvarId_3395_ = stack[1].m_obj;
lean_object* v_a_3396_ = stack[2].m_obj;
lean_object* v_a_3397_ = stack[3].m_obj;
lean_object* v_a_3398_ = stack[4].m_obj;
lean_object* v_res_3519_;
v_res_3519_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3394_, v_fvarId_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
stack->m_obj
 = v_res_3519_;
}
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t v___x_3520_, lean_object* v_m_3521_, lean_object* v_e_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
lean_object* v___y_3528_; uint8_t v___x_3532_; 
v___x_3532_ = l_Lean_Expr_hasFVar(v_e_3522_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_dec_ref(v_m_3521_);
v___x_3533_ = lean_box(v___x_3532_);
v___x_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
lean_ctor_set(v___x_3534_, 1, v___y_3523_);
v___x_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
return v___x_3535_;
}
else
{
uint8_t v___x_3536_; 
v___x_3536_ = l_Lean_Expr_isFVar(v_e_3522_);
if (v___x_3536_ == 0)
{
lean_dec_ref(v_m_3521_);
v___y_3528_ = v___y_3523_;
goto v___jp_3527_;
}
else
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = l_Lean_Expr_fvarId_x21(v_e_3522_);
v___x_3538_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3521_, v___x_3537_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___x_3537_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v_snd_3540_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3539_);
lean_dec_ref_known(v___x_3538_, 1);
v_snd_3540_ = lean_ctor_get(v_a_3539_, 1);
lean_inc(v_snd_3540_);
lean_dec(v_a_3539_);
v___y_3528_ = v_snd_3540_;
goto v___jp_3527_;
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
v_a_3541_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3538_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3538_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
v___jp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3529_ = lean_box(v___x_3520_);
v___x_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
lean_ctor_set(v___x_3530_, 1, v___y_3528_);
v___x_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
return v___x_3531_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3520_ = stack[0].m_num;
lean_object* v_m_3521_ = stack[1].m_obj;
lean_object* v_e_3522_ = stack[2].m_obj;
lean_object* v___y_3523_ = stack[3].m_obj;
lean_object* v___y_3524_ = stack[4].m_obj;
lean_object* v___y_3525_ = stack[5].m_obj;
lean_object* v_res_3549_;
v_res_3549_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(v___x_3520_, v_m_3521_, v_e_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
stack->m_obj
 = v_res_3549_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object* v_m_3550_, lean_object* v_fvarId_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3550_, v_fvarId_3551_, v_a_3552_, v_a_3553_, v_a_3554_);
lean_dec(v_a_3554_);
lean_dec_ref(v_a_3553_);
lean_dec(v_fvarId_3551_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object* v_00_u03b2_3557_, lean_object* v_m_3558_, lean_object* v_a_3559_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3558_, v_a_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object* v_00_u03b2_3561_, lean_object* v_m_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(v_00_u03b2_3561_, v_m_3562_, v_a_3563_);
lean_dec(v_a_3563_);
lean_dec_ref(v_m_3562_);
return v_res_3564_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object* v_00_u03b2_3565_, lean_object* v_m_3566_, lean_object* v_a_3567_){
_start:
{
uint8_t v___x_3568_; 
v___x_3568_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_3566_, v_a_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_3566_ = stack[1].m_obj;
lean_object* v_a_3567_ = stack[2].m_obj;
uint8_t v_res_3569_;
v_res_3569_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_box(0), v_m_3566_, v_a_3567_);
stack->m_num = v_res_3569_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object* v_00_u03b2_3570_, lean_object* v_m_3571_, lean_object* v_a_3572_){
_start:
{
uint8_t v_res_3573_; lean_object* v_r_3574_; 
v_res_3573_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(v_00_u03b2_3570_, v_m_3571_, v_a_3572_);
lean_dec(v_a_3572_);
lean_dec_ref(v_m_3571_);
v_r_3574_ = lean_box(v_res_3573_);
return v_r_3574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object* v_00_u03b2_3575_, lean_object* v_m_3576_, lean_object* v_a_3577_, lean_object* v_b_3578_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_m_3576_, v_a_3577_, v_b_3578_);
return v___x_3579_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object* v_00_u03b1_3580_, lean_object* v_msg_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3581_, v___y_3583_, v___y_3584_);
return v___x_3586_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3581_ = stack[1].m_obj;
lean_object* v___y_3582_ = stack[2].m_obj;
lean_object* v___y_3583_ = stack[3].m_obj;
lean_object* v___y_3584_ = stack[4].m_obj;
lean_object* v_res_3587_;
v_res_3587_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_box(0), v_msg_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
stack->m_obj
 = v_res_3587_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object* v_00_u03b1_3588_, lean_object* v_msg_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v_00_u03b1_3588_, v_msg_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3590_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object* v_00_u03b2_3595_, lean_object* v_a_3596_, lean_object* v_x_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3596_, v_x_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3599_, lean_object* v_a_3600_, lean_object* v_x_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(v_00_u03b2_3599_, v_a_3600_, v_x_3601_);
lean_dec(v_x_3601_);
lean_dec(v_a_3600_);
return v_res_3602_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_object* v_00_u03b2_3603_, lean_object* v_a_3604_, lean_object* v_x_3605_){
_start:
{
uint8_t v___x_3606_; 
v___x_3606_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3604_, v_x_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3604_ = stack[1].m_obj;
lean_object* v_x_3605_ = stack[2].m_obj;
uint8_t v_res_3607_;
v_res_3607_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_box(0), v_a_3604_, v_x_3605_);
stack->m_num = v_res_3607_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3608_, lean_object* v_a_3609_, lean_object* v_x_3610_){
_start:
{
uint8_t v_res_3611_; lean_object* v_r_3612_; 
v_res_3611_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(v_00_u03b2_3608_, v_a_3609_, v_x_3610_);
lean_dec(v_x_3610_);
lean_dec(v_a_3609_);
v_r_3612_ = lean_box(v_res_3611_);
return v_r_3612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(lean_object* v_00_u03b2_3613_, lean_object* v_data_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_data_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(lean_object* v_00_u03b2_3616_, lean_object* v_m_3617_, lean_object* v_a_3618_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_3617_, v_a_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3620_, lean_object* v_m_3621_, lean_object* v_a_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(v_00_u03b2_3620_, v_m_3621_, v_a_3622_);
lean_dec_ref(v_a_3622_);
lean_dec_ref(v_m_3621_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(lean_object* v_00_u03b2_3624_, lean_object* v_m_3625_, lean_object* v_a_3626_, lean_object* v_b_3627_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_3625_, v_a_3626_, v_b_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_3629_, lean_object* v_i_3630_, lean_object* v_source_3631_, lean_object* v_target_3632_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v_i_3630_, v_source_3631_, v_target_3632_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_3634_, lean_object* v_a_3635_, lean_object* v_x_3636_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_3635_, v_x_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3638_, lean_object* v_a_3639_, lean_object* v_x_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(v_00_u03b2_3638_, v_a_3639_, v_x_3640_);
lean_dec(v_x_3640_);
lean_dec_ref(v_a_3639_);
return v_res_3641_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3642_, lean_object* v_a_3643_, lean_object* v_x_3644_){
_start:
{
uint8_t v___x_3645_; 
v___x_3645_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3643_, v_x_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3643_ = stack[1].m_obj;
lean_object* v_x_3644_ = stack[2].m_obj;
uint8_t v_res_3646_;
v_res_3646_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(lean_box(0), v_a_3643_, v_x_3644_);
stack->m_num = v_res_3646_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3647_, lean_object* v_a_3648_, lean_object* v_x_3649_){
_start:
{
uint8_t v_res_3650_; lean_object* v_r_3651_; 
v_res_3650_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(v_00_u03b2_3647_, v_a_3648_, v_x_3649_);
lean_dec(v_x_3649_);
lean_dec_ref(v_a_3648_);
v_r_3651_ = lean_box(v_res_3650_);
return v_r_3651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b2_3652_, lean_object* v_data_3653_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_data_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13(lean_object* v_00_u03b2_3655_, lean_object* v_a_3656_, lean_object* v_b_3657_, lean_object* v_x_3658_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3656_, v_b_3657_, v_x_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_3660_, lean_object* v_x_3661_, lean_object* v_x_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_x_3661_, v_x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17(lean_object* v_00_u03b2_3664_, lean_object* v_i_3665_, lean_object* v_source_3666_, lean_object* v_target_3667_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v_i_3665_, v_source_3666_, v_target_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18(lean_object* v_00_u03b2_3669_, lean_object* v_x_3670_, lean_object* v_x_3671_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_x_3670_, v_x_3671_);
return v___x_3672_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object* v_msg_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v___f_3678_; lean_object* v___x_7408__overap_3679_; lean_object* v___x_3680_; 
v___f_3678_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___closed__0));
v___x_7408__overap_3679_ = lean_panic_fn_borrowed(v___f_3678_, v_msg_3674_);
lean_inc(v___y_3676_);
lean_inc_ref(v___y_3675_);
v___x_3680_ = lean_apply_3(v___x_7408__overap_3679_, v___y_3675_, v___y_3676_, lean_box(0));
return v___x_3680_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3674_ = stack[0].m_obj;
lean_object* v___y_3675_ = stack[1].m_obj;
lean_object* v___y_3676_ = stack[2].m_obj;
lean_object* v_res_3681_;
v_res_3681_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v_msg_3674_, v___y_3675_, v___y_3676_);
stack->m_obj
 = v_res_3681_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___boxed(lean_object* v_msg_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v_msg_3682_, v___y_3683_, v___y_3684_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
return v_res_3686_;
}
}
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object* v_newDecls_3687_, lean_object* v_newArgs_3688_, lean_object* v_____r_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3694_, 0, v_newDecls_3687_);
lean_ctor_set(v___x_3694_, 1, v_newArgs_3688_);
v___x_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
lean_ctor_set(v___x_3695_, 1, v___y_3690_);
v___x_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_newDecls_3687_ = stack[0].m_obj;
lean_object* v_newArgs_3688_ = stack[1].m_obj;
lean_object* v_____r_3689_ = stack[2].m_obj;
lean_object* v___y_3690_ = stack[3].m_obj;
lean_object* v___y_3691_ = stack[4].m_obj;
lean_object* v___y_3692_ = stack[5].m_obj;
lean_object* v_res_3697_;
v_res_3697_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3687_, v_newArgs_3688_, v_____r_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
stack->m_obj
 = v_res_3697_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object* v_newDecls_3698_, lean_object* v_newArgs_3699_, lean_object* v_____r_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3698_, v_newArgs_3699_, v_____r_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
return v_res_3705_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(lean_object* v_cls_3706_, lean_object* v_msg_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_ref_3711_; lean_object* v___x_3712_; lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3758_; 
v_ref_3711_ = lean_ctor_get(v___y_3708_, 2);
v___x_3712_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3707_, v___y_3708_, v___y_3709_);
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3758_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3758_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; lean_object* v_traceState_3718_; lean_object* v_env_3719_; lean_object* v_nextMacroScope_3720_; lean_object* v_ngen_3721_; lean_object* v_auxDeclNGen_3722_; lean_object* v_cache_3723_; lean_object* v_recordedDeps_3724_; lean_object* v_messages_3725_; lean_object* v_infoState_3726_; lean_object* v_snapshotTasks_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3757_; 
v___x_3717_ = lean_st_ref_take(v___y_3709_);
v_traceState_3718_ = lean_ctor_get(v___x_3717_, 4);
v_env_3719_ = lean_ctor_get(v___x_3717_, 0);
v_nextMacroScope_3720_ = lean_ctor_get(v___x_3717_, 1);
v_ngen_3721_ = lean_ctor_get(v___x_3717_, 2);
v_auxDeclNGen_3722_ = lean_ctor_get(v___x_3717_, 3);
v_cache_3723_ = lean_ctor_get(v___x_3717_, 5);
v_recordedDeps_3724_ = lean_ctor_get(v___x_3717_, 6);
v_messages_3725_ = lean_ctor_get(v___x_3717_, 7);
v_infoState_3726_ = lean_ctor_get(v___x_3717_, 8);
v_snapshotTasks_3727_ = lean_ctor_get(v___x_3717_, 9);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3729_ = v___x_3717_;
v_isShared_3730_ = v_isSharedCheck_3757_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_snapshotTasks_3727_);
lean_inc(v_infoState_3726_);
lean_inc(v_messages_3725_);
lean_inc(v_recordedDeps_3724_);
lean_inc(v_cache_3723_);
lean_inc(v_traceState_3718_);
lean_inc(v_auxDeclNGen_3722_);
lean_inc(v_ngen_3721_);
lean_inc(v_nextMacroScope_3720_);
lean_inc(v_env_3719_);
lean_dec(v___x_3717_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3757_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
uint64_t v_tid_3731_; lean_object* v_traces_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3756_; 
v_tid_3731_ = lean_ctor_get_uint64(v_traceState_3718_, sizeof(void*)*1);
v_traces_3732_ = lean_ctor_get(v_traceState_3718_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_traceState_3718_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3734_ = v_traceState_3718_;
v_isShared_3735_ = v_isSharedCheck_3756_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_traces_3732_);
lean_dec(v_traceState_3718_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3756_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; double v___x_3738_; uint8_t v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
v___x_3736_ = lean_box(0);
v___x_3737_ = lean_box(0);
v___x_3738_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3739_ = 0;
v___x_3740_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3741_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3741_, 0, v_cls_3706_);
lean_ctor_set(v___x_3741_, 1, v___x_3737_);
lean_ctor_set(v___x_3741_, 2, v___x_3740_);
lean_ctor_set_float(v___x_3741_, sizeof(void*)*3, v___x_3738_);
lean_ctor_set_float(v___x_3741_, sizeof(void*)*3 + 8, v___x_3738_);
lean_ctor_set_uint8(v___x_3741_, sizeof(void*)*3 + 16, v___x_3739_);
v___x_3742_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3743_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3741_);
lean_ctor_set(v___x_3743_, 1, v_a_3713_);
lean_ctor_set(v___x_3743_, 2, v___x_3742_);
lean_inc(v_ref_3711_);
v___x_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3744_, 0, v_ref_3711_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = l_Lean_PersistentArray_push___redArg(v_traces_3732_, v___x_3744_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 0, v___x_3745_);
v___x_3747_ = v___x_3734_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3745_);
lean_ctor_set_uint64(v_reuseFailAlloc_3755_, sizeof(void*)*1, v_tid_3731_);
v___x_3747_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3749_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 4, v___x_3747_);
v___x_3749_ = v___x_3729_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_env_3719_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v_nextMacroScope_3720_);
lean_ctor_set(v_reuseFailAlloc_3754_, 2, v_ngen_3721_);
lean_ctor_set(v_reuseFailAlloc_3754_, 3, v_auxDeclNGen_3722_);
lean_ctor_set(v_reuseFailAlloc_3754_, 4, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3754_, 5, v_cache_3723_);
lean_ctor_set(v_reuseFailAlloc_3754_, 6, v_recordedDeps_3724_);
lean_ctor_set(v_reuseFailAlloc_3754_, 7, v_messages_3725_);
lean_ctor_set(v_reuseFailAlloc_3754_, 8, v_infoState_3726_);
lean_ctor_set(v_reuseFailAlloc_3754_, 9, v_snapshotTasks_3727_);
v___x_3749_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3750_; lean_object* v___x_3752_; 
v___x_3750_ = lean_st_ref_put(v___y_3709_, v___x_3749_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3736_);
v___x_3752_ = v___x_3715_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3736_);
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
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3706_ = stack[0].m_obj;
lean_object* v_msg_3707_ = stack[1].m_obj;
lean_object* v___y_3708_ = stack[2].m_obj;
lean_object* v___y_3709_ = stack[3].m_obj;
lean_object* v_res_3759_;
v_res_3759_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3706_, v_msg_3707_, v___y_3708_, v___y_3709_);
stack->m_obj
 = v_res_3759_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(lean_object* v_cls_3760_, lean_object* v_msg_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3760_, v_msg_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
return v_res_3765_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(size_t v_sz_3766_, size_t v_i_3767_, lean_object* v_bs_3768_){
_start:
{
uint8_t v___x_3769_; 
v___x_3769_ = lean_usize_dec_lt(v_i_3767_, v_sz_3766_);
if (v___x_3769_ == 0)
{
return v_bs_3768_;
}
else
{
lean_object* v_v_3770_; lean_object* v___x_3771_; lean_object* v_bs_x27_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; size_t v___x_3775_; size_t v___x_3776_; lean_object* v___x_3777_; 
v_v_3770_ = lean_array_uget(v_bs_3768_, v_i_3767_);
v___x_3771_ = lean_unsigned_to_nat(0u);
v_bs_x27_3772_ = lean_array_uset(v_bs_3768_, v_i_3767_, v___x_3771_);
v___x_3773_ = l_Lean_LocalDecl_fvarId(v_v_3770_);
lean_dec(v_v_3770_);
v___x_3774_ = l_Lean_mkFVar(v___x_3773_);
v___x_3775_ = ((size_t)1ULL);
v___x_3776_ = lean_usize_add(v_i_3767_, v___x_3775_);
v___x_3777_ = lean_array_uset(v_bs_x27_3772_, v_i_3767_, v___x_3774_);
v_i_3767_ = v___x_3776_;
v_bs_3768_ = v___x_3777_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3766_ = stack[0].m_num;
size_t v_i_3767_ = stack[1].m_num;
lean_object* v_bs_3768_ = stack[2].m_obj;
lean_object* v_res_3779_;
v_res_3779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_3766_, v_i_3767_, v_bs_3768_);
stack->m_obj
 = v_res_3779_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(lean_object* v_sz_3780_, lean_object* v_i_3781_, lean_object* v_bs_3782_){
_start:
{
size_t v_sz_boxed_3783_; size_t v_i_boxed_3784_; lean_object* v_res_3785_; 
v_sz_boxed_3783_ = lean_unbox_usize(v_sz_3780_);
lean_dec(v_sz_3780_);
v_i_boxed_3784_ = lean_unbox_usize(v_i_3781_);
lean_dec(v_i_3781_);
v_res_3785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_boxed_3783_, v_i_boxed_3784_, v_bs_3782_);
return v_res_3785_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(lean_object* v___x_3786_, lean_object* v_as_3787_, size_t v_sz_3788_, size_t v_i_3789_, lean_object* v_b_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
uint8_t v___x_3795_; 
v___x_3795_ = lean_usize_dec_lt(v_i_3789_, v_sz_3788_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
lean_dec_ref(v___x_3786_);
v___x_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3796_, 0, v_b_3790_);
lean_ctor_set(v___x_3796_, 1, v___y_3791_);
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
return v___x_3797_;
}
else
{
lean_object* v___x_3798_; lean_object* v_a_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3798_ = lean_box(0);
v_a_3799_ = lean_array_uget_borrowed(v_as_3787_, v_i_3789_);
v___x_3800_ = l_Lean_LocalDecl_fvarId(v_a_3799_);
lean_inc_ref(v___x_3786_);
v___x_3801_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v___x_3786_, v___x_3800_, v___y_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___x_3800_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v_snd_3803_; size_t v___x_3804_; size_t v___x_3805_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v_snd_3803_ = lean_ctor_get(v_a_3802_, 1);
lean_inc(v_snd_3803_);
lean_dec(v_a_3802_);
v___x_3804_ = ((size_t)1ULL);
v___x_3805_ = lean_usize_add(v_i_3789_, v___x_3804_);
v_i_3789_ = v___x_3805_;
v_b_3790_ = v___x_3798_;
v___y_3791_ = v_snd_3803_;
goto _start;
}
else
{
lean_dec_ref(v___x_3786_);
return v___x_3801_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3786_ = stack[0].m_obj;
lean_object* v_as_3787_ = stack[1].m_obj;
size_t v_sz_3788_ = stack[2].m_num;
size_t v_i_3789_ = stack[3].m_num;
lean_object* v_b_3790_ = stack[4].m_obj;
lean_object* v___y_3791_ = stack[5].m_obj;
lean_object* v___y_3792_ = stack[6].m_obj;
lean_object* v___y_3793_ = stack[7].m_obj;
lean_object* v_res_3807_;
v_res_3807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v___x_3786_, v_as_3787_, v_sz_3788_, v_i_3789_, v_b_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
stack->m_obj
 = v_res_3807_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object* v___x_3808_, lean_object* v_as_3809_, lean_object* v_sz_3810_, lean_object* v_i_3811_, lean_object* v_b_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
size_t v_sz_boxed_3817_; size_t v_i_boxed_3818_; lean_object* v_res_3819_; 
v_sz_boxed_3817_ = lean_unbox_usize(v_sz_3810_);
lean_dec(v_sz_3810_);
v_i_boxed_3818_ = lean_unbox_usize(v_i_3811_);
lean_dec(v_i_3811_);
v_res_3819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v___x_3808_, v_as_3809_, v_sz_boxed_3817_, v_i_boxed_3818_, v_b_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec_ref(v_as_3809_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object* v_a_3820_, lean_object* v_a_3821_){
_start:
{
if (lean_obj_tag(v_a_3820_) == 0)
{
lean_object* v___x_3822_; 
v___x_3822_ = l_List_reverse___redArg(v_a_3821_);
return v___x_3822_;
}
else
{
lean_object* v_head_3823_; lean_object* v_tail_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3833_; 
v_head_3823_ = lean_ctor_get(v_a_3820_, 0);
v_tail_3824_ = lean_ctor_get(v_a_3820_, 1);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_a_3820_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3826_ = v_a_3820_;
v_isShared_3827_ = v_isSharedCheck_3833_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_tail_3824_);
lean_inc(v_head_3823_);
lean_dec(v_a_3820_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3833_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3828_; lean_object* v___x_3830_; 
v___x_3828_ = l_Lean_MessageData_ofExpr(v_head_3823_);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 1, v_a_3821_);
lean_ctor_set(v___x_3826_, 0, v___x_3828_);
v___x_3830_ = v___x_3826_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3828_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_a_3821_);
v___x_3830_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
v_a_3820_ = v_tail_3824_;
v_a_3821_ = v___x_3830_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(lean_object* v_a_3834_, lean_object* v_b_3835_, lean_object* v_x_3836_){
_start:
{
if (lean_obj_tag(v_x_3836_) == 0)
{
lean_dec(v_b_3835_);
lean_dec(v_a_3834_);
return v_x_3836_;
}
else
{
lean_object* v_key_3837_; lean_object* v_value_3838_; lean_object* v_tail_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3851_; 
v_key_3837_ = lean_ctor_get(v_x_3836_, 0);
v_value_3838_ = lean_ctor_get(v_x_3836_, 1);
v_tail_3839_ = lean_ctor_get(v_x_3836_, 2);
v_isSharedCheck_3851_ = !lean_is_exclusive(v_x_3836_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3841_ = v_x_3836_;
v_isShared_3842_ = v_isSharedCheck_3851_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_tail_3839_);
lean_inc(v_value_3838_);
lean_inc(v_key_3837_);
lean_dec(v_x_3836_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3851_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
uint8_t v___x_3843_; 
v___x_3843_ = l_Lean_instBEqFVarId_beq(v_key_3837_, v_a_3834_);
if (v___x_3843_ == 0)
{
lean_object* v___x_3844_; lean_object* v___x_3846_; 
v___x_3844_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_3834_, v_b_3835_, v_tail_3839_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 2, v___x_3844_);
v___x_3846_ = v___x_3841_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_key_3837_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_value_3838_);
lean_ctor_set(v_reuseFailAlloc_3847_, 2, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
else
{
lean_object* v___x_3849_; 
lean_dec(v_value_3838_);
lean_dec(v_key_3837_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 1, v_b_3835_);
lean_ctor_set(v___x_3841_, 0, v_a_3834_);
v___x_3849_ = v___x_3841_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3834_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_b_3835_);
lean_ctor_set(v_reuseFailAlloc_3850_, 2, v_tail_3839_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(lean_object* v_m_3852_, lean_object* v_a_3853_, lean_object* v_b_3854_){
_start:
{
lean_object* v_size_3855_; lean_object* v_buckets_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3899_; 
v_size_3855_ = lean_ctor_get(v_m_3852_, 0);
v_buckets_3856_ = lean_ctor_get(v_m_3852_, 1);
v_isSharedCheck_3899_ = !lean_is_exclusive(v_m_3852_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3858_ = v_m_3852_;
v_isShared_3859_ = v_isSharedCheck_3899_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_buckets_3856_);
lean_inc(v_size_3855_);
lean_dec(v_m_3852_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3899_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3860_; uint64_t v___x_3861_; uint64_t v___x_3862_; uint64_t v___x_3863_; uint64_t v_fold_3864_; uint64_t v___x_3865_; uint64_t v___x_3866_; uint64_t v___x_3867_; size_t v___x_3868_; size_t v___x_3869_; size_t v___x_3870_; size_t v___x_3871_; size_t v___x_3872_; lean_object* v_bkt_3873_; uint8_t v___x_3874_; 
v___x_3860_ = lean_array_get_size(v_buckets_3856_);
v___x_3861_ = l_Lean_instHashableFVarId_hash(v_a_3853_);
v___x_3862_ = 32ULL;
v___x_3863_ = lean_uint64_shift_right(v___x_3861_, v___x_3862_);
v_fold_3864_ = lean_uint64_xor(v___x_3861_, v___x_3863_);
v___x_3865_ = 16ULL;
v___x_3866_ = lean_uint64_shift_right(v_fold_3864_, v___x_3865_);
v___x_3867_ = lean_uint64_xor(v_fold_3864_, v___x_3866_);
v___x_3868_ = lean_uint64_to_usize(v___x_3867_);
v___x_3869_ = lean_usize_of_nat(v___x_3860_);
v___x_3870_ = ((size_t)1ULL);
v___x_3871_ = lean_usize_sub(v___x_3869_, v___x_3870_);
v___x_3872_ = lean_usize_land(v___x_3868_, v___x_3871_);
v_bkt_3873_ = lean_array_uget_borrowed(v_buckets_3856_, v___x_3872_);
v___x_3874_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3853_, v_bkt_3873_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; lean_object* v_size_x27_3876_; lean_object* v___x_3877_; lean_object* v_buckets_x27_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; uint8_t v___x_3884_; 
v___x_3875_ = lean_unsigned_to_nat(1u);
v_size_x27_3876_ = lean_nat_add(v_size_3855_, v___x_3875_);
lean_dec(v_size_3855_);
lean_inc(v_bkt_3873_);
v___x_3877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3877_, 0, v_a_3853_);
lean_ctor_set(v___x_3877_, 1, v_b_3854_);
lean_ctor_set(v___x_3877_, 2, v_bkt_3873_);
v_buckets_x27_3878_ = lean_array_uset(v_buckets_3856_, v___x_3872_, v___x_3877_);
v___x_3879_ = lean_unsigned_to_nat(4u);
v___x_3880_ = lean_nat_mul(v_size_x27_3876_, v___x_3879_);
v___x_3881_ = lean_unsigned_to_nat(3u);
v___x_3882_ = lean_nat_div(v___x_3880_, v___x_3881_);
lean_dec(v___x_3880_);
v___x_3883_ = lean_array_get_size(v_buckets_x27_3878_);
v___x_3884_ = lean_nat_dec_le(v___x_3882_, v___x_3883_);
lean_dec(v___x_3882_);
if (v___x_3884_ == 0)
{
lean_object* v_val_3885_; lean_object* v___x_3887_; 
v_val_3885_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_3878_);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 1, v_val_3885_);
lean_ctor_set(v___x_3858_, 0, v_size_x27_3876_);
v___x_3887_ = v___x_3858_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_size_x27_3876_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_val_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
else
{
lean_object* v___x_3890_; 
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 1, v_buckets_x27_3878_);
lean_ctor_set(v___x_3858_, 0, v_size_x27_3876_);
v___x_3890_ = v___x_3858_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_size_x27_3876_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_buckets_x27_3878_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
else
{
lean_object* v___x_3892_; lean_object* v_buckets_x27_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3897_; 
lean_inc(v_bkt_3873_);
v___x_3892_ = lean_box(0);
v_buckets_x27_3893_ = lean_array_uset(v_buckets_3856_, v___x_3872_, v___x_3892_);
v___x_3894_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_3853_, v_b_3854_, v_bkt_3873_);
v___x_3895_ = lean_array_uset(v_buckets_x27_3893_, v___x_3872_, v___x_3894_);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 1, v___x_3895_);
v___x_3897_ = v___x_3858_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_size_3855_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(lean_object* v_as_3900_, size_t v_sz_3901_, size_t v_i_3902_, lean_object* v_b_3903_){
_start:
{
uint8_t v___x_3905_; 
v___x_3905_ = lean_usize_dec_lt(v_i_3902_, v_sz_3901_);
if (v___x_3905_ == 0)
{
lean_object* v___x_3906_; 
v___x_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3906_, 0, v_b_3903_);
return v___x_3906_;
}
else
{
lean_object* v_snd_3907_; lean_object* v_fst_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3943_; 
v_snd_3907_ = lean_ctor_get(v_b_3903_, 1);
v_fst_3908_ = lean_ctor_get(v_b_3903_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v_b_3903_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3910_ = v_b_3903_;
v_isShared_3911_ = v_isSharedCheck_3943_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_snd_3907_);
lean_inc(v_fst_3908_);
lean_dec(v_b_3903_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3943_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v_array_3912_; lean_object* v_start_3913_; lean_object* v_stop_3914_; uint8_t v___x_3915_; 
v_array_3912_ = lean_ctor_get(v_snd_3907_, 0);
v_start_3913_ = lean_ctor_get(v_snd_3907_, 1);
v_stop_3914_ = lean_ctor_get(v_snd_3907_, 2);
v___x_3915_ = lean_nat_dec_lt(v_start_3913_, v_stop_3914_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3917_; 
if (v_isShared_3911_ == 0)
{
v___x_3917_ = v___x_3910_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_fst_3908_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v_snd_3907_);
v___x_3917_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3918_; 
v___x_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
return v___x_3918_;
}
}
else
{
lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3939_; 
lean_inc(v_stop_3914_);
lean_inc(v_start_3913_);
lean_inc_ref(v_array_3912_);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_snd_3907_);
if (v_isSharedCheck_3939_ == 0)
{
lean_object* v_unused_3940_; lean_object* v_unused_3941_; lean_object* v_unused_3942_; 
v_unused_3940_ = lean_ctor_get(v_snd_3907_, 2);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v_snd_3907_, 1);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v_snd_3907_, 0);
lean_dec(v_unused_3942_);
v___x_3921_ = v_snd_3907_;
v_isShared_3922_ = v_isSharedCheck_3939_;
goto v_resetjp_3920_;
}
else
{
lean_dec(v_snd_3907_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3939_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v_a_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
v_a_3923_ = lean_array_uget_borrowed(v_as_3900_, v_i_3902_);
v___x_3924_ = lean_array_fget(v_array_3912_, v_start_3913_);
v___x_3925_ = lean_unsigned_to_nat(1u);
v___x_3926_ = lean_nat_add(v_start_3913_, v___x_3925_);
lean_dec(v_start_3913_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 1, v___x_3926_);
v___x_3928_ = v___x_3921_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_array_3912_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3938_, 2, v_stop_3914_);
v___x_3928_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3929_ = l_Lean_LocalDecl_fvarId(v_a_3923_);
lean_inc(v_a_3923_);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 1, v___x_3924_);
lean_ctor_set(v___x_3910_, 0, v_a_3923_);
v___x_3931_ = v___x_3910_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3923_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v___x_3924_);
v___x_3931_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; size_t v___x_3934_; size_t v___x_3935_; 
v___x_3932_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(v_fst_3908_, v___x_3929_, v___x_3931_);
v___x_3933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
lean_ctor_set(v___x_3933_, 1, v___x_3928_);
v___x_3934_ = ((size_t)1ULL);
v___x_3935_ = lean_usize_add(v_i_3902_, v___x_3934_);
v_i_3902_ = v___x_3935_;
v_b_3903_ = v___x_3933_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3900_ = stack[0].m_obj;
size_t v_sz_3901_ = stack[1].m_num;
size_t v_i_3902_ = stack[2].m_num;
lean_object* v_b_3903_ = stack[3].m_obj;
lean_object* v_res_3944_;
v_res_3944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_3900_, v_sz_3901_, v_i_3902_, v_b_3903_);
stack->m_obj
 = v_res_3944_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg___boxed(lean_object* v_as_3945_, lean_object* v_sz_3946_, lean_object* v_i_3947_, lean_object* v_b_3948_, lean_object* v___y_3949_){
_start:
{
size_t v_sz_boxed_3950_; size_t v_i_boxed_3951_; lean_object* v_res_3952_; 
v_sz_boxed_3950_ = lean_unbox_usize(v_sz_3946_);
lean_dec(v_sz_3946_);
v_i_boxed_3951_ = lean_unbox_usize(v_i_3947_);
lean_dec(v_i_3947_);
v_res_3952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_3945_, v_sz_boxed_3950_, v_i_boxed_3951_, v_b_3948_);
lean_dec_ref(v_as_3945_);
return v_res_3952_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2(void){
_start:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3955_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1));
v___x_3956_ = lean_unsigned_to_nat(2u);
v___x_3957_ = lean_unsigned_to_nat(372u);
v___x_3958_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3959_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3960_ = l_mkPanicMessageWithDecl(v___x_3959_, v___x_3958_, v___x_3957_, v___x_3956_, v___x_3955_);
return v___x_3960_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4(void){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3962_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3));
v___x_3963_ = lean_unsigned_to_nat(2u);
v___x_3964_ = lean_unsigned_to_nat(373u);
v___x_3965_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3966_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3967_ = l_mkPanicMessageWithDecl(v___x_3966_, v___x_3965_, v___x_3964_, v___x_3963_, v___x_3962_);
return v___x_3967_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5(void){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3968_ = lean_box(0);
v___x_3969_ = lean_unsigned_to_nat(16u);
v___x_3970_ = lean_mk_array(v___x_3969_, v___x_3968_);
return v___x_3970_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6(void){
_start:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3971_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5);
v___x_3972_ = lean_unsigned_to_nat(0u);
v___x_3973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
lean_ctor_set(v___x_3973_, 1, v___x_3971_);
return v___x_3973_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8(void){
_start:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7));
v___x_3976_ = l_Lean_stringToMessageData(v___x_3975_);
return v___x_3976_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9));
v___x_3979_ = l_Lean_stringToMessageData(v___x_3978_);
return v___x_3979_;
}
}
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object* v_sortedDecls_3980_, lean_object* v_sortedArgs_3981_, lean_object* v_toSortDecls_3982_, lean_object* v_toSortArgs_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_){
_start:
{
lean_object* v___y_3988_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v_snd_4011_; lean_object* v___x_4013_; lean_object* v___x_4014_; uint8_t v___x_4015_; 
v___x_4013_ = lean_array_get_size(v_sortedDecls_3980_);
v___x_4014_ = lean_array_get_size(v_sortedArgs_3981_);
v___x_4015_ = lean_nat_dec_eq(v___x_4013_, v___x_4014_);
if (v___x_4015_ == 0)
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
lean_dec_ref(v_toSortArgs_3983_);
lean_dec_ref(v_sortedArgs_3981_);
lean_dec_ref(v_sortedDecls_3980_);
v___x_4016_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2);
v___x_4017_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v___x_4016_, v_a_3984_, v_a_3985_);
return v___x_4017_;
}
else
{
lean_object* v___x_4018_; lean_object* v___x_4019_; uint8_t v___x_4020_; 
v___x_4018_ = lean_array_get_size(v_toSortDecls_3982_);
v___x_4019_ = lean_array_get_size(v_toSortArgs_3983_);
v___x_4020_ = lean_nat_dec_eq(v___x_4018_, v___x_4019_);
if (v___x_4020_ == 0)
{
lean_object* v___x_4021_; lean_object* v___x_4022_; 
lean_dec_ref(v_toSortArgs_3983_);
lean_dec_ref(v_sortedArgs_3981_);
lean_dec_ref(v_sortedDecls_3980_);
v___x_4021_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4);
v___x_4022_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v___x_4021_, v_a_3984_, v_a_3985_);
return v___x_4022_;
}
else
{
lean_object* v___x_4023_; uint8_t v___x_4024_; 
v___x_4023_ = lean_unsigned_to_nat(0u);
v___x_4024_ = lean_nat_dec_eq(v___x_4018_, v___x_4023_);
if (v___x_4024_ == 0)
{
lean_object* v_toCold_4025_; lean_object* v_options_4026_; lean_object* v_inheritedTraceOptions_4027_; uint8_t v_hasTrace_4028_; lean_object* v___x_4029_; lean_object* v_cls_4030_; lean_object* v___y_4032_; lean_object* v___y_4033_; 
v_toCold_4025_ = lean_ctor_get(v_a_3984_, 0);
v_options_4026_ = lean_ctor_get(v_toCold_4025_, 2);
v_inheritedTraceOptions_4027_ = lean_ctor_get(v_toCold_4025_, 11);
v_hasTrace_4028_ = lean_ctor_get_uint8(v_options_4026_, sizeof(void*)*1);
v___x_4029_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_cls_4030_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
if (v_hasTrace_4028_ == 0)
{
v___y_4032_ = v_a_3984_;
v___y_4033_ = v_a_3985_;
goto v___jp_4031_;
}
else
{
lean_object* v___x_4134_; uint8_t v___x_4135_; 
v___x_4134_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4135_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4027_, v_options_4026_, v___x_4134_);
if (v___x_4135_ == 0)
{
v___y_4032_ = v_a_3984_;
v___y_4033_ = v_a_3985_;
goto v___jp_4031_;
}
else
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10);
v___x_4137_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_4030_, v___x_4136_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_dec_ref_known(v___x_4137_, 1);
v___y_4032_ = v_a_3984_;
v___y_4033_ = v_a_3985_;
goto v___jp_4031_;
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec_ref(v_toSortArgs_3983_);
lean_dec_ref(v_sortedArgs_3981_);
lean_dec_ref(v_sortedDecls_3980_);
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4137_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4137_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
}
v___jp_4031_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; size_t v_sz_4037_; size_t v___x_4038_; lean_object* v___x_4039_; 
v___x_4034_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6);
v___x_4035_ = l_Array_toSubarray___redArg(v_sortedArgs_3981_, v___x_4023_, v___x_4014_);
v___x_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4034_);
lean_ctor_set(v___x_4036_, 1, v___x_4035_);
v_sz_4037_ = lean_array_size(v_sortedDecls_3980_);
v___x_4038_ = ((size_t)0ULL);
v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_sortedDecls_3980_, v_sz_4037_, v___x_4038_, v___x_4036_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v_fst_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4124_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref_known(v___x_4039_, 1);
v_fst_4041_ = lean_ctor_get(v_a_4040_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v_a_4040_);
if (v_isSharedCheck_4124_ == 0)
{
lean_object* v_unused_4125_; 
v_unused_4125_ = lean_ctor_get(v_a_4040_, 1);
lean_dec(v_unused_4125_);
v___x_4043_ = v_a_4040_;
v_isShared_4044_ = v_isSharedCheck_4124_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_fst_4041_);
lean_dec(v_a_4040_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4124_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; lean_object* v___x_4047_; 
v___x_4045_ = l_Array_toSubarray___redArg(v_toSortArgs_3983_, v___x_4023_, v___x_4019_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 1, v___x_4045_);
v___x_4047_ = v___x_4043_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_fst_4041_);
lean_ctor_set(v_reuseFailAlloc_4123_, 1, v___x_4045_);
v___x_4047_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
size_t v_sz_4048_; lean_object* v___x_4049_; 
v_sz_4048_ = lean_array_size(v_toSortDecls_3982_);
v___x_4049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_toSortDecls_3982_, v_sz_4048_, v___x_4038_, v___x_4047_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v_fst_4051_; lean_object* v_size_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___x_4049_, 1);
v_fst_4051_ = lean_ctor_get(v_a_4050_, 0);
lean_inc_n(v_fst_4051_, 2);
lean_dec(v_a_4050_);
v_size_4052_ = lean_ctor_get(v_fst_4051_, 0);
v___x_4053_ = lean_mk_empty_array_with_capacity(v_size_4052_);
lean_inc_ref(v___x_4053_);
v___x_4054_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4029_);
lean_ctor_set(v___x_4054_, 1, v___x_4029_);
lean_ctor_set(v___x_4054_, 2, v___x_4053_);
lean_ctor_set(v___x_4054_, 3, v___x_4053_);
v___x_4055_ = lean_box(0);
v___x_4056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_4051_, v_sortedDecls_3980_, v_sz_4037_, v___x_4038_, v___x_4055_, v___x_4054_, v___y_4032_, v___y_4033_);
lean_dec_ref(v_sortedDecls_3980_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v_snd_4058_; lean_object* v___x_4059_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref_known(v___x_4056_, 1);
v_snd_4058_ = lean_ctor_get(v_a_4057_, 1);
lean_inc(v_snd_4058_);
lean_dec(v_a_4057_);
v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_4051_, v_toSortDecls_3982_, v_sz_4048_, v___x_4038_, v___x_4055_, v_snd_4058_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; lean_object* v_snd_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4097_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_a_4060_);
lean_dec_ref_known(v___x_4059_, 1);
v_snd_4061_ = lean_ctor_get(v_a_4060_, 1);
v_isSharedCheck_4097_ = !lean_is_exclusive(v_a_4060_);
if (v_isSharedCheck_4097_ == 0)
{
lean_object* v_unused_4098_; 
v_unused_4098_ = lean_ctor_get(v_a_4060_, 0);
lean_dec(v_unused_4098_);
v___x_4063_ = v_a_4060_;
v_isShared_4064_ = v_isSharedCheck_4097_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_snd_4061_);
lean_dec(v_a_4060_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4097_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v_toCold_4065_; lean_object* v_options_4066_; lean_object* v_newDecls_4067_; lean_object* v_newArgs_4068_; lean_object* v_inheritedTraceOptions_4069_; uint8_t v_hasTrace_4070_; lean_object* v___f_4071_; 
v_toCold_4065_ = lean_ctor_get(v___y_4032_, 0);
v_options_4066_ = lean_ctor_get(v_toCold_4065_, 2);
v_newDecls_4067_ = lean_ctor_get(v_snd_4061_, 2);
v_newArgs_4068_ = lean_ctor_get(v_snd_4061_, 3);
v_inheritedTraceOptions_4069_ = lean_ctor_get(v_toCold_4065_, 11);
v_hasTrace_4070_ = lean_ctor_get_uint8(v_options_4066_, sizeof(void*)*1);
lean_inc_ref(v_newArgs_4068_);
lean_inc_ref(v_newDecls_4067_);
v___f_4071_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4071_, 0, v_newDecls_4067_);
lean_closure_set(v___f_4071_, 1, v_newArgs_4068_);
if (v_hasTrace_4070_ == 0)
{
lean_del_object(v___x_4063_);
v___y_4007_ = v___f_4071_;
v___y_4008_ = v___y_4032_;
v___y_4009_ = v___x_4055_;
v___y_4010_ = v___y_4033_;
v_snd_4011_ = v_snd_4061_;
goto v___jp_4006_;
}
else
{
lean_object* v___x_4072_; uint8_t v___x_4073_; 
v___x_4072_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4073_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4069_, v_options_4066_, v___x_4072_);
if (v___x_4073_ == 0)
{
lean_del_object(v___x_4063_);
v___y_4007_ = v___f_4071_;
v___y_4008_ = v___y_4032_;
v___y_4009_ = v___x_4055_;
v___y_4010_ = v___y_4033_;
v_snd_4011_ = v_snd_4061_;
goto v___jp_4006_;
}
else
{
lean_object* v___x_4074_; size_t v_sz_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4082_; 
lean_inc_ref(v_newArgs_4068_);
lean_inc_ref_n(v_newDecls_4067_, 2);
lean_dec_ref(v___f_4071_);
v___x_4074_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8);
v_sz_4075_ = lean_array_size(v_newDecls_4067_);
v___x_4076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_4075_, v___x_4038_, v_newDecls_4067_);
v___x_4077_ = lean_array_to_list(v___x_4076_);
v___x_4078_ = lean_box(0);
v___x_4079_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v___x_4077_, v___x_4078_);
v___x_4080_ = l_Lean_MessageData_ofList(v___x_4079_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set_tag(v___x_4063_, 7);
lean_ctor_set(v___x_4063_, 1, v___x_4080_);
lean_ctor_set(v___x_4063_, 0, v___x_4074_);
v___x_4082_ = v___x_4063_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4074_);
lean_ctor_set(v_reuseFailAlloc_4096_, 1, v___x_4080_);
v___x_4082_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_4030_, v___x_4082_, v_snd_4061_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v_fst_4085_; lean_object* v_snd_4086_; lean_object* v___x_4087_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref_known(v___x_4083_, 1);
v_fst_4085_ = lean_ctor_get(v_a_4084_, 0);
lean_inc(v_fst_4085_);
v_snd_4086_ = lean_ctor_get(v_a_4084_, 1);
lean_inc(v_snd_4086_);
lean_dec(v_a_4084_);
v___x_4087_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_4067_, v_newArgs_4068_, v_fst_4085_, v_snd_4086_, v___y_4032_, v___y_4033_);
v___y_3988_ = v___x_4087_;
goto v___jp_3987_;
}
else
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4095_; 
lean_dec_ref(v_newArgs_4068_);
lean_dec_ref(v_newDecls_4067_);
v_a_4088_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4090_ = v___x_4083_;
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4083_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4093_; 
if (v_isShared_4091_ == 0)
{
v___x_4093_ = v___x_4090_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4088_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
return v___x_4093_;
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
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
v_a_4099_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4059_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4059_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec(v_fst_4051_);
v_a_4107_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4056_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4056_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
lean_dec_ref(v_sortedDecls_3980_);
v_a_4115_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4049_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4049_);
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
}
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
lean_dec_ref(v_toSortArgs_3983_);
lean_dec_ref(v_sortedDecls_3980_);
v_a_4126_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4039_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4039_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
else
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
lean_dec_ref(v_toSortArgs_3983_);
v___x_4146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4146_, 0, v_sortedDecls_3980_);
lean_ctor_set(v___x_4146_, 1, v_sortedArgs_3981_);
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
return v___x_4147_;
}
}
}
v___jp_3987_:
{
if (lean_obj_tag(v___y_3988_) == 0)
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3997_; 
v_a_3989_ = lean_ctor_get(v___y_3988_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___y_3988_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3991_ = v___y_3988_;
v_isShared_3992_ = v_isSharedCheck_3997_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___y_3988_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3997_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v_fst_3993_; lean_object* v___x_3995_; 
v_fst_3993_ = lean_ctor_get(v_a_3989_, 0);
lean_inc(v_fst_3993_);
lean_dec(v_a_3989_);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 0, v_fst_3993_);
v___x_3995_ = v___x_3991_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_fst_3993_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
v_a_3998_ = lean_ctor_get(v___y_3988_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___y_3988_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___y_3988_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___y_3988_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
v___jp_4006_:
{
lean_object* v___x_4012_; 
lean_inc(v___y_4010_);
lean_inc_ref(v___y_4008_);
v___x_4012_ = lean_apply_5(v___y_4007_, v___y_4009_, v_snd_4011_, v___y_4008_, v___y_4010_, lean_box(0));
v___y_3988_ = v___x_4012_;
goto v___jp_3987_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_0interp(lean_interpreter_value* stack)
{
lean_object* v_sortedDecls_3980_ = stack[0].m_obj;
lean_object* v_sortedArgs_3981_ = stack[1].m_obj;
lean_object* v_toSortDecls_3982_ = stack[2].m_obj;
lean_object* v_toSortArgs_3983_ = stack[3].m_obj;
lean_object* v_a_3984_ = stack[4].m_obj;
lean_object* v_a_3985_ = stack[5].m_obj;
lean_object* v_res_4148_;
v_res_4148_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v_sortedDecls_3980_, v_sortedArgs_3981_, v_toSortDecls_3982_, v_toSortArgs_3983_, v_a_3984_, v_a_3985_);
stack->m_obj
 = v_res_4148_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object* v_sortedDecls_4149_, lean_object* v_sortedArgs_4150_, lean_object* v_toSortDecls_4151_, lean_object* v_toSortArgs_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v_sortedDecls_4149_, v_sortedArgs_4150_, v_toSortDecls_4151_, v_toSortArgs_4152_, v_a_4153_, v_a_4154_);
lean_dec(v_a_4154_);
lean_dec_ref(v_a_4153_);
lean_dec_ref(v_toSortDecls_4151_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object* v_00_u03b2_4157_, lean_object* v_m_4158_, lean_object* v_a_4159_, lean_object* v_b_4160_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(v_m_4158_, v_a_4159_, v_b_4160_);
return v___x_4161_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object* v_as_4162_, size_t v_sz_4163_, size_t v_i_4164_, lean_object* v_b_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_4162_, v_sz_4163_, v_i_4164_, v_b_4165_);
return v___x_4169_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4162_ = stack[0].m_obj;
size_t v_sz_4163_ = stack[1].m_num;
size_t v_i_4164_ = stack[2].m_num;
lean_object* v_b_4165_ = stack[3].m_obj;
lean_object* v___y_4166_ = stack[4].m_obj;
lean_object* v___y_4167_ = stack[5].m_obj;
lean_object* v_res_4170_;
v_res_4170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_as_4162_, v_sz_4163_, v_i_4164_, v_b_4165_, v___y_4166_, v___y_4167_);
stack->m_obj
 = v_res_4170_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object* v_as_4171_, lean_object* v_sz_4172_, lean_object* v_i_4173_, lean_object* v_b_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
size_t v_sz_boxed_4178_; size_t v_i_boxed_4179_; lean_object* v_res_4180_; 
v_sz_boxed_4178_ = lean_unbox_usize(v_sz_4172_);
lean_dec(v_sz_4172_);
v_i_boxed_4179_ = lean_unbox_usize(v_i_4173_);
lean_dec(v_i_4173_);
v_res_4180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_as_4171_, v_sz_boxed_4178_, v_i_boxed_4179_, v_b_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec_ref(v_as_4171_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0(lean_object* v_00_u03b2_4181_, lean_object* v_a_4182_, lean_object* v_b_4183_, lean_object* v_x_4184_){
_start:
{
lean_object* v___x_4185_; 
v___x_4185_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_4182_, v_b_4183_, v_x_4184_);
return v___x_4185_;
}
}
lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(lean_object* v_msg_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v___f_4193_; lean_object* v___x_1735__overap_4194_; lean_object* v___x_4195_; 
v___f_4193_ = ((lean_object*)(l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1___closed__0));
v___x_1735__overap_4194_ = lean_panic_fn_borrowed(v___f_4193_, v_msg_4187_);
lean_inc(v___y_4191_);
lean_inc_ref(v___y_4190_);
lean_inc(v___y_4189_);
lean_inc_ref(v___y_4188_);
v___x_4195_ = lean_apply_5(v___x_1735__overap_4194_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, lean_box(0));
return v___x_4195_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4187_ = stack[0].m_obj;
lean_object* v___y_4188_ = stack[1].m_obj;
lean_object* v___y_4189_ = stack[2].m_obj;
lean_object* v___y_4190_ = stack[3].m_obj;
lean_object* v___y_4191_ = stack[4].m_obj;
lean_object* v_res_4196_;
v_res_4196_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(v_msg_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
stack->m_obj
 = v_res_4196_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1___boxed(lean_object* v_msg_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(v_msg_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
return v_res_4203_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(lean_object* v_as_4204_, size_t v_i_4205_, size_t v_stop_4206_){
_start:
{
uint8_t v___x_4211_; 
v___x_4211_ = lean_usize_dec_eq(v_i_4205_, v_stop_4206_);
if (v___x_4211_ == 0)
{
lean_object* v___x_4212_; 
v___x_4212_ = lean_array_uget_borrowed(v_as_4204_, v_i_4205_);
if (lean_obj_tag(v___x_4212_) == 0)
{
goto v___jp_4207_;
}
else
{
lean_object* v_val_4213_; uint8_t v___x_4214_; 
v_val_4213_ = lean_ctor_get(v___x_4212_, 0);
v___x_4214_ = l_Lean_LocalDecl_isLet(v_val_4213_, v___x_4211_);
if (v___x_4214_ == 0)
{
goto v___jp_4207_;
}
else
{
return v___x_4214_;
}
}
}
else
{
uint8_t v___x_4215_; 
v___x_4215_ = 0;
return v___x_4215_;
}
v___jp_4207_:
{
size_t v___x_4208_; size_t v___x_4209_; 
v___x_4208_ = ((size_t)1ULL);
v___x_4209_ = lean_usize_add(v_i_4205_, v___x_4208_);
v_i_4205_ = v___x_4209_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4204_ = stack[0].m_obj;
size_t v_i_4205_ = stack[1].m_num;
size_t v_stop_4206_ = stack[2].m_num;
uint8_t v_res_4216_;
v_res_4216_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_as_4204_, v_i_4205_, v_stop_4206_);
stack->m_num = v_res_4216_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1___boxed(lean_object* v_as_4217_, lean_object* v_i_4218_, lean_object* v_stop_4219_){
_start:
{
size_t v_i_boxed_4220_; size_t v_stop_boxed_4221_; uint8_t v_res_4222_; lean_object* v_r_4223_; 
v_i_boxed_4220_ = lean_unbox_usize(v_i_4218_);
lean_dec(v_i_4218_);
v_stop_boxed_4221_ = lean_unbox_usize(v_stop_4219_);
lean_dec(v_stop_4219_);
v_res_4222_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_as_4217_, v_i_boxed_4220_, v_stop_boxed_4221_);
lean_dec_ref(v_as_4217_);
v_r_4223_ = lean_box(v_res_4222_);
return v_r_4223_;
}
}
uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(lean_object* v_x_4224_){
_start:
{
if (lean_obj_tag(v_x_4224_) == 0)
{
lean_object* v_cs_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; uint8_t v___x_4228_; 
v_cs_4225_ = lean_ctor_get(v_x_4224_, 0);
v___x_4226_ = lean_unsigned_to_nat(0u);
v___x_4227_ = lean_array_get_size(v_cs_4225_);
v___x_4228_ = lean_nat_dec_lt(v___x_4226_, v___x_4227_);
if (v___x_4228_ == 0)
{
return v___x_4228_;
}
else
{
if (v___x_4228_ == 0)
{
return v___x_4228_;
}
else
{
size_t v___x_4229_; size_t v___x_4230_; uint8_t v___x_4231_; 
v___x_4229_ = ((size_t)0ULL);
v___x_4230_ = lean_usize_of_nat(v___x_4227_);
v___x_4231_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(v_cs_4225_, v___x_4229_, v___x_4230_);
return v___x_4231_;
}
}
}
else
{
lean_object* v_vs_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; uint8_t v___x_4235_; 
v_vs_4232_ = lean_ctor_get(v_x_4224_, 0);
v___x_4233_ = lean_unsigned_to_nat(0u);
v___x_4234_ = lean_array_get_size(v_vs_4232_);
v___x_4235_ = lean_nat_dec_lt(v___x_4233_, v___x_4234_);
if (v___x_4235_ == 0)
{
return v___x_4235_;
}
else
{
if (v___x_4235_ == 0)
{
return v___x_4235_;
}
else
{
size_t v___x_4236_; size_t v___x_4237_; uint8_t v___x_4238_; 
v___x_4236_ = ((size_t)0ULL);
v___x_4237_ = lean_usize_of_nat(v___x_4234_);
v___x_4238_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_vs_4232_, v___x_4236_, v___x_4237_);
return v___x_4238_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4224_ = stack[0].m_obj;
uint8_t v_res_4239_;
v_res_4239_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v_x_4224_);
stack->m_num = v_res_4239_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(lean_object* v_as_4240_, size_t v_i_4241_, size_t v_stop_4242_){
_start:
{
uint8_t v___x_4243_; 
v___x_4243_ = lean_usize_dec_eq(v_i_4241_, v_stop_4242_);
if (v___x_4243_ == 0)
{
lean_object* v___x_4244_; uint8_t v___x_4245_; 
v___x_4244_ = lean_array_uget_borrowed(v_as_4240_, v_i_4241_);
v___x_4245_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v___x_4244_);
if (v___x_4245_ == 0)
{
size_t v___x_4246_; size_t v___x_4247_; 
v___x_4246_ = ((size_t)1ULL);
v___x_4247_ = lean_usize_add(v_i_4241_, v___x_4246_);
v_i_4241_ = v___x_4247_;
goto _start;
}
else
{
return v___x_4245_;
}
}
else
{
uint8_t v___x_4249_; 
v___x_4249_ = 0;
return v___x_4249_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4240_ = stack[0].m_obj;
size_t v_i_4241_ = stack[1].m_num;
size_t v_stop_4242_ = stack[2].m_num;
uint8_t v_res_4250_;
v_res_4250_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(v_as_4240_, v_i_4241_, v_stop_4242_);
stack->m_num = v_res_4250_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4251_, lean_object* v_i_4252_, lean_object* v_stop_4253_){
_start:
{
size_t v_i_boxed_4254_; size_t v_stop_boxed_4255_; uint8_t v_res_4256_; lean_object* v_r_4257_; 
v_i_boxed_4254_ = lean_unbox_usize(v_i_4252_);
lean_dec(v_i_4252_);
v_stop_boxed_4255_ = lean_unbox_usize(v_stop_4253_);
lean_dec(v_stop_4253_);
v_res_4256_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0_spec__2(v_as_4251_, v_i_boxed_4254_, v_stop_boxed_4255_);
lean_dec_ref(v_as_4251_);
v_r_4257_ = lean_box(v_res_4256_);
return v_r_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0___boxed(lean_object* v_x_4258_){
_start:
{
uint8_t v_res_4259_; lean_object* v_r_4260_; 
v_res_4259_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v_x_4258_);
lean_dec_ref(v_x_4258_);
v_r_4260_ = lean_box(v_res_4259_);
return v_r_4260_;
}
}
uint8_t l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object* v_t_4261_){
_start:
{
lean_object* v_root_4262_; lean_object* v_tail_4263_; uint8_t v___x_4264_; 
v_root_4262_ = lean_ctor_get(v_t_4261_, 0);
v_tail_4263_ = lean_ctor_get(v_t_4261_, 1);
v___x_4264_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__0(v_root_4262_);
if (v___x_4264_ == 0)
{
lean_object* v___x_4265_; lean_object* v___x_4266_; uint8_t v___x_4267_; 
v___x_4265_ = lean_unsigned_to_nat(0u);
v___x_4266_ = lean_array_get_size(v_tail_4263_);
v___x_4267_ = lean_nat_dec_lt(v___x_4265_, v___x_4266_);
if (v___x_4267_ == 0)
{
return v___x_4267_;
}
else
{
if (v___x_4267_ == 0)
{
return v___x_4267_;
}
else
{
size_t v___x_4268_; size_t v___x_4269_; uint8_t v___x_4270_; 
v___x_4268_ = ((size_t)0ULL);
v___x_4269_ = lean_usize_of_nat(v___x_4266_);
v___x_4270_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_spec__1(v_tail_4263_, v___x_4268_, v___x_4269_);
return v___x_4270_;
}
}
}
else
{
return v___x_4264_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_4261_ = stack[0].m_obj;
uint8_t v_res_4271_;
v_res_4271_ = l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_t_4261_);
stack->m_num = v_res_4271_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object* v_t_4272_){
_start:
{
uint8_t v_res_4273_; lean_object* v_r_4274_; 
v_res_4273_ = l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_t_4272_);
lean_dec_ref(v_t_4272_);
v_r_4274_ = lean_box(v_res_4273_);
return v_r_4274_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0(void){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = lean_box(0);
v___x_4276_ = lean_unsigned_to_nat(16u);
v___x_4277_ = lean_mk_array(v___x_4276_, v___x_4275_);
return v___x_4277_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1(void){
_start:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4278_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0);
v___x_4279_ = lean_unsigned_to_nat(0u);
v___x_4280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
lean_ctor_set(v___x_4280_, 1, v___x_4278_);
return v___x_4280_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3(void){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4283_ = lean_unsigned_to_nat(1u);
v___x_4284_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2));
v___x_4285_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
v___x_4286_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4285_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
lean_ctor_set(v___x_4286_, 2, v___x_4284_);
lean_ctor_set(v___x_4286_, 3, v___x_4283_);
lean_ctor_set(v___x_4286_, 4, v___x_4284_);
lean_ctor_set(v___x_4286_, 5, v___x_4284_);
lean_ctor_set(v___x_4286_, 6, v___x_4284_);
lean_ctor_set(v___x_4286_, 7, v___x_4284_);
lean_ctor_set(v___x_4286_, 8, v___x_4283_);
lean_ctor_set(v___x_4286_, 9, v___x_4284_);
lean_ctor_set(v___x_4286_, 10, v___x_4284_);
lean_ctor_set(v___x_4286_, 11, v___x_4284_);
return v___x_4286_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6(void){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4289_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5));
v___x_4290_ = lean_unsigned_to_nat(2u);
v___x_4291_ = lean_unsigned_to_nat(424u);
v___x_4292_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__4));
v___x_4293_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_4294_ = l_mkPanicMessageWithDecl(v___x_4293_, v___x_4292_, v___x_4291_, v___x_4290_, v___x_4289_);
return v___x_4294_;
}
}
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* v_type_4295_, lean_object* v_value_4296_, uint8_t v_zetaDelta_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v_lctx_4303_; lean_object* v_decls_4304_; uint8_t v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v_lctx_4303_ = lean_ctor_get(v_a_4298_, 2);
v_decls_4304_ = lean_ctor_get(v_lctx_4303_, 1);
v___x_4305_ = l_Lean_PersistentArray_anyM___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_decls_4304_);
v___x_4306_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4306_, 0, v_zetaDelta_4297_);
lean_ctor_set_uint8(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__3, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3);
v___x_4308_ = lean_st_mk_ref(v___x_4307_);
v___x_4309_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_4295_, v_value_4296_, v___x_4306_, v___x_4308_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_);
lean_dec_ref_known(v___x_4306_, 0);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4311_; lean_object* v_fst_4312_; lean_object* v_snd_4313_; lean_object* v_levelParams_4314_; lean_object* v_levelArgs_4315_; lean_object* v_newLocalDecls_4316_; lean_object* v_newLocalDeclsForMVars_4317_; lean_object* v_newLetDecls_4318_; lean_object* v_exprMVarArgs_4319_; lean_object* v_exprFVarArgs_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___x_4309_, 1);
v___x_4311_ = lean_st_ref_get(v___x_4308_);
lean_dec(v___x_4308_);
v_fst_4312_ = lean_ctor_get(v_a_4310_, 0);
lean_inc(v_fst_4312_);
v_snd_4313_ = lean_ctor_get(v_a_4310_, 1);
lean_inc(v_snd_4313_);
lean_dec(v_a_4310_);
v_levelParams_4314_ = lean_ctor_get(v___x_4311_, 2);
lean_inc_ref(v_levelParams_4314_);
v_levelArgs_4315_ = lean_ctor_get(v___x_4311_, 4);
lean_inc_ref(v_levelArgs_4315_);
v_newLocalDecls_4316_ = lean_ctor_get(v___x_4311_, 5);
lean_inc_ref(v_newLocalDecls_4316_);
v_newLocalDeclsForMVars_4317_ = lean_ctor_get(v___x_4311_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_4317_);
v_newLetDecls_4318_ = lean_ctor_get(v___x_4311_, 7);
lean_inc_ref(v_newLetDecls_4318_);
v_exprMVarArgs_4319_ = lean_ctor_get(v___x_4311_, 9);
lean_inc_ref(v_exprMVarArgs_4319_);
v_exprFVarArgs_4320_ = lean_ctor_get(v___x_4311_, 10);
lean_inc_ref(v_exprFVarArgs_4320_);
lean_dec(v___x_4311_);
v___x_4321_ = l_Array_reverse___redArg(v_newLocalDecls_4316_);
v___x_4322_ = l_Array_reverse___redArg(v_exprFVarArgs_4320_);
v___x_4323_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v___x_4321_, v___x_4322_, v_newLocalDeclsForMVars_4317_, v_exprMVarArgs_4319_, v_a_4300_, v_a_4301_);
lean_dec_ref(v_newLocalDeclsForMVars_4317_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4342_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4326_ = v___x_4323_;
v_isShared_4327_ = v_isSharedCheck_4342_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4323_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4342_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v_fst_4328_; lean_object* v_snd_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; uint8_t v___x_4335_; 
v_fst_4328_ = lean_ctor_get(v_a_4324_, 0);
lean_inc_n(v_fst_4328_, 2);
v_snd_4329_ = lean_ctor_get(v_a_4324_, 1);
lean_inc(v_snd_4329_);
lean_dec(v_a_4324_);
v___x_4330_ = l_Array_reverse___redArg(v_newLetDecls_4318_);
lean_inc_ref(v___x_4330_);
v___x_4331_ = l_Lean_Meta_Closure_mkForall(v___x_4330_, v_fst_4312_);
lean_dec(v_fst_4312_);
v___x_4332_ = l_Lean_Meta_Closure_mkForall(v_fst_4328_, v___x_4331_);
lean_dec_ref(v___x_4331_);
v___x_4333_ = l_Lean_Meta_Closure_mkLambda(v___x_4330_, v_snd_4313_);
lean_dec(v_snd_4313_);
v___x_4334_ = l_Lean_Meta_Closure_mkLambda(v_fst_4328_, v___x_4333_);
lean_dec_ref(v___x_4333_);
v___x_4335_ = l_Lean_Expr_hasFVar(v___x_4334_);
if (v___x_4335_ == 0)
{
lean_object* v___x_4336_; lean_object* v___x_4338_; 
v___x_4336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4336_, 0, v_levelParams_4314_);
lean_ctor_set(v___x_4336_, 1, v___x_4332_);
lean_ctor_set(v___x_4336_, 2, v___x_4334_);
lean_ctor_set(v___x_4336_, 3, v_levelArgs_4315_);
lean_ctor_set(v___x_4336_, 4, v_snd_4329_);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v___x_4336_);
v___x_4338_ = v___x_4326_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v___x_4336_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
else
{
lean_object* v___x_4340_; lean_object* v___x_4341_; 
lean_dec_ref(v___x_4334_);
lean_dec_ref(v___x_4332_);
lean_dec(v_snd_4329_);
lean_del_object(v___x_4326_);
lean_dec_ref(v_levelArgs_4315_);
lean_dec_ref(v_levelParams_4314_);
v___x_4340_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__6, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6);
v___x_4341_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__1(v___x_4340_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_);
return v___x_4341_;
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec_ref(v_newLetDecls_4318_);
lean_dec_ref(v_levelArgs_4315_);
lean_dec_ref(v_levelParams_4314_);
lean_dec(v_snd_4313_);
lean_dec(v_fst_4312_);
v_a_4343_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4323_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4323_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
lean_dec(v___x_4308_);
v_a_4351_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4309_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4309_);
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
LEAN_EXPORT void l_Lean_Meta_Closure_mkValueTypeClosure_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_4295_ = stack[0].m_obj;
lean_object* v_value_4296_ = stack[1].m_obj;
uint8_t v_zetaDelta_4297_ = stack[2].m_num;
lean_object* v_a_4298_ = stack[3].m_obj;
lean_object* v_a_4299_ = stack[4].m_obj;
lean_object* v_a_4300_ = stack[5].m_obj;
lean_object* v_a_4301_ = stack[6].m_obj;
lean_object* v_res_4359_;
v_res_4359_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4295_, v_value_4296_, v_zetaDelta_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_);
stack->m_obj
 = v_res_4359_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* v_type_4360_, lean_object* v_value_4361_, lean_object* v_zetaDelta_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
uint8_t v_zetaDelta_boxed_4368_; lean_object* v_res_4369_; 
v_zetaDelta_boxed_4368_ = lean_unbox(v_zetaDelta_4362_);
v_res_4369_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4360_, v_value_4361_, v_zetaDelta_boxed_4368_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
lean_dec(v_a_4366_);
lean_dec_ref(v_a_4365_);
lean_dec(v_a_4364_);
lean_dec_ref(v_a_4363_);
return v_res_4369_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* v_name_4370_, lean_object* v_levelParams_4371_, lean_object* v_type_4372_, lean_object* v_value_4373_, lean_object* v_hints_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v___x_4377_; uint8_t v___y_4379_; uint8_t v___y_4386_; lean_object* v_env_4389_; uint8_t v___x_4390_; 
v___x_4377_ = lean_st_ref_get(v___y_4375_);
v_env_4389_ = lean_ctor_get(v___x_4377_, 0);
lean_inc_ref_n(v_env_4389_, 2);
lean_dec(v___x_4377_);
v___x_4390_ = l_Lean_Environment_hasUnsafe(v_env_4389_, v_type_4372_);
if (v___x_4390_ == 0)
{
uint8_t v___x_4391_; 
v___x_4391_ = l_Lean_Environment_hasUnsafe(v_env_4389_, v_value_4373_);
v___y_4386_ = v___x_4391_;
goto v___jp_4385_;
}
else
{
lean_dec_ref(v_env_4389_);
v___y_4386_ = v___x_4390_;
goto v___jp_4385_;
}
v___jp_4378_:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
lean_inc(v_name_4370_);
v___x_4380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4380_, 0, v_name_4370_);
lean_ctor_set(v___x_4380_, 1, v_levelParams_4371_);
lean_ctor_set(v___x_4380_, 2, v_type_4372_);
v___x_4381_ = lean_box(0);
v___x_4382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4382_, 0, v_name_4370_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
v___x_4383_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4383_, 0, v___x_4380_);
lean_ctor_set(v___x_4383_, 1, v_value_4373_);
lean_ctor_set(v___x_4383_, 2, v_hints_4374_);
lean_ctor_set(v___x_4383_, 3, v___x_4382_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*4, v___y_4379_);
v___x_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4383_);
return v___x_4384_;
}
v___jp_4385_:
{
if (v___y_4386_ == 0)
{
uint8_t v___x_4387_; 
v___x_4387_ = 1;
v___y_4379_ = v___x_4387_;
goto v___jp_4378_;
}
else
{
uint8_t v___x_4388_; 
v___x_4388_ = 0;
v___y_4379_ = v___x_4388_;
goto v___jp_4378_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4370_ = stack[0].m_obj;
lean_object* v_levelParams_4371_ = stack[1].m_obj;
lean_object* v_type_4372_ = stack[2].m_obj;
lean_object* v_value_4373_ = stack[3].m_obj;
lean_object* v_hints_4374_ = stack[4].m_obj;
lean_object* v___y_4375_ = stack[5].m_obj;
lean_object* v_res_4392_;
v_res_4392_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4370_, v_levelParams_4371_, v_type_4372_, v_value_4373_, v_hints_4374_, v___y_4375_);
stack->m_obj
 = v_res_4392_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* v_name_4393_, lean_object* v_levelParams_4394_, lean_object* v_type_4395_, lean_object* v_value_4396_, lean_object* v_hints_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4393_, v_levelParams_4394_, v_type_4395_, v_value_4396_, v_hints_4397_, v___y_4398_);
lean_dec(v___y_4398_);
return v_res_4400_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(lean_object* v_name_4401_, lean_object* v_levelParams_4402_, lean_object* v_type_4403_, lean_object* v_value_4404_, lean_object* v_hints_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v___x_4411_; 
v___x_4411_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4401_, v_levelParams_4402_, v_type_4403_, v_value_4404_, v_hints_4405_, v___y_4409_);
return v___x_4411_;
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4401_ = stack[0].m_obj;
lean_object* v_levelParams_4402_ = stack[1].m_obj;
lean_object* v_type_4403_ = stack[2].m_obj;
lean_object* v_value_4404_ = stack[3].m_obj;
lean_object* v_hints_4405_ = stack[4].m_obj;
lean_object* v___y_4406_ = stack[5].m_obj;
lean_object* v___y_4407_ = stack[6].m_obj;
lean_object* v___y_4408_ = stack[7].m_obj;
lean_object* v___y_4409_ = stack[8].m_obj;
lean_object* v_res_4412_;
v_res_4412_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(v_name_4401_, v_levelParams_4402_, v_type_4403_, v_value_4404_, v_hints_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
stack->m_obj
 = v_res_4412_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* v_name_4413_, lean_object* v_levelParams_4414_, lean_object* v_type_4415_, lean_object* v_value_4416_, lean_object* v_hints_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(v_name_4413_, v_levelParams_4414_, v_type_4415_, v_value_4416_, v_hints_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
return v_res_4423_;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* v_name_4424_, lean_object* v_type_4425_, lean_object* v_value_4426_, uint8_t v_zetaDelta_4427_, uint8_t v_compile_4428_, uint8_t v_logCompileErrors_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4425_, v_value_4426_, v_zetaDelta_4427_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4487_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4438_ = v___x_4435_;
v_isShared_4439_ = v_isSharedCheck_4487_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4435_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4487_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4449_; lean_object* v_env_4450_; lean_object* v_levelParams_4451_; lean_object* v_type_4452_; lean_object* v_value_4453_; uint32_t v___x_4454_; uint32_t v___x_4455_; uint32_t v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4486_; 
v___x_4449_ = lean_st_ref_get(v_a_4433_);
v_env_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc_ref(v_env_4450_);
lean_dec(v___x_4449_);
v_levelParams_4451_ = lean_ctor_get(v_a_4436_, 0);
v_type_4452_ = lean_ctor_get(v_a_4436_, 1);
v_value_4453_ = lean_ctor_get(v_a_4436_, 2);
lean_inc_ref_n(v_value_4453_, 2);
v___x_4454_ = l_Lean_getMaxHeight(v_env_4450_, v_value_4453_);
v___x_4455_ = 1;
v___x_4456_ = lean_uint32_add(v___x_4454_, v___x_4455_);
v___x_4457_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4457_, 0, v___x_4456_);
lean_inc_ref(v_levelParams_4451_);
v___x_4458_ = lean_array_to_list(v_levelParams_4451_);
lean_inc_ref(v_type_4452_);
lean_inc(v_name_4424_);
v___x_4459_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4424_, v___x_4458_, v_type_4452_, v_value_4453_, v___x_4457_, v_a_4433_);
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4462_ = v___x_4459_;
v_isShared_4463_ = v_isSharedCheck_4486_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4459_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4486_;
goto v_resetjp_4461_;
}
v___jp_4440_:
{
lean_object* v_levelArgs_4441_; lean_object* v_exprArgs_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4447_; 
v_levelArgs_4441_ = lean_ctor_get(v_a_4436_, 3);
lean_inc_ref(v_levelArgs_4441_);
v_exprArgs_4442_ = lean_ctor_get(v_a_4436_, 4);
lean_inc_ref(v_exprArgs_4442_);
lean_dec(v_a_4436_);
v___x_4443_ = lean_array_to_list(v_levelArgs_4441_);
v___x_4444_ = l_Lean_mkConst(v_name_4424_, v___x_4443_);
v___x_4445_ = l_Lean_mkAppN(v___x_4444_, v_exprArgs_4442_);
lean_dec_ref(v_exprArgs_4442_);
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4445_);
v___x_4447_ = v___x_4438_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v___x_4445_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
lean_ctor_set_tag(v___x_4462_, 1);
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
uint8_t v___x_4466_; lean_object* v___x_4467_; 
v___x_4466_ = 0;
lean_inc_ref(v___x_4465_);
v___x_4467_ = l_Lean_addDecl(v___x_4465_, v___x_4466_, v_a_4432_, v_a_4433_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_dec_ref_known(v___x_4467_, 1);
if (v_compile_4428_ == 0)
{
lean_dec_ref(v___x_4465_);
goto v___jp_4440_;
}
else
{
lean_object* v___x_4468_; 
v___x_4468_ = l_Lean_compileDecl(v___x_4465_, v_logCompileErrors_4429_, v_a_4432_, v_a_4433_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_dec_ref_known(v___x_4468_, 1);
goto v___jp_4440_;
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_del_object(v___x_4438_);
lean_dec(v_a_4436_);
lean_dec(v_name_4424_);
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4468_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4468_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
}
else
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
lean_dec_ref(v___x_4465_);
lean_del_object(v___x_4438_);
lean_dec(v_a_4436_);
lean_dec(v_name_4424_);
v_a_4477_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4467_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4467_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
lean_dec(v_name_4424_);
v_a_4488_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4490_ = v___x_4435_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4435_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkAuxDefinition_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4424_ = stack[0].m_obj;
lean_object* v_type_4425_ = stack[1].m_obj;
lean_object* v_value_4426_ = stack[2].m_obj;
uint8_t v_zetaDelta_4427_ = stack[3].m_num;
uint8_t v_compile_4428_ = stack[4].m_num;
uint8_t v_logCompileErrors_4429_ = stack[5].m_num;
lean_object* v_a_4430_ = stack[6].m_obj;
lean_object* v_a_4431_ = stack[7].m_obj;
lean_object* v_a_4432_ = stack[8].m_obj;
lean_object* v_a_4433_ = stack[9].m_obj;
lean_object* v_res_4496_;
v_res_4496_ = l_Lean_Meta_mkAuxDefinition(v_name_4424_, v_type_4425_, v_value_4426_, v_zetaDelta_4427_, v_compile_4428_, v_logCompileErrors_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
stack->m_obj
 = v_res_4496_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* v_name_4497_, lean_object* v_type_4498_, lean_object* v_value_4499_, lean_object* v_zetaDelta_4500_, lean_object* v_compile_4501_, lean_object* v_logCompileErrors_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_){
_start:
{
uint8_t v_zetaDelta_boxed_4508_; uint8_t v_compile_boxed_4509_; uint8_t v_logCompileErrors_boxed_4510_; lean_object* v_res_4511_; 
v_zetaDelta_boxed_4508_ = lean_unbox(v_zetaDelta_4500_);
v_compile_boxed_4509_ = lean_unbox(v_compile_4501_);
v_logCompileErrors_boxed_4510_ = lean_unbox(v_logCompileErrors_4502_);
v_res_4511_ = l_Lean_Meta_mkAuxDefinition(v_name_4497_, v_type_4498_, v_value_4499_, v_zetaDelta_boxed_4508_, v_compile_boxed_4509_, v_logCompileErrors_boxed_4510_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
return v_res_4511_;
}
}
lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* v_name_4512_, lean_object* v_value_4513_, uint8_t v_zetaDelta_4514_, uint8_t v_compile_4515_, uint8_t v_logCompileErrors_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_){
_start:
{
lean_object* v___x_4522_; 
lean_inc(v_a_4520_);
lean_inc_ref(v_a_4519_);
lean_inc(v_a_4518_);
lean_inc_ref(v_a_4517_);
lean_inc_ref(v_value_4513_);
v___x_4522_ = lean_infer_type(v_value_4513_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
lean_inc(v_a_4523_);
lean_dec_ref_known(v___x_4522_, 1);
v___x_4524_ = l_Lean_Expr_headBeta(v_a_4523_);
v___x_4525_ = l_Lean_Meta_mkAuxDefinition(v_name_4512_, v___x_4524_, v_value_4513_, v_zetaDelta_4514_, v_compile_4515_, v_logCompileErrors_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
return v___x_4525_;
}
else
{
lean_dec_ref(v_value_4513_);
lean_dec(v_name_4512_);
return v___x_4522_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkAuxDefinitionFor_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4512_ = stack[0].m_obj;
lean_object* v_value_4513_ = stack[1].m_obj;
uint8_t v_zetaDelta_4514_ = stack[2].m_num;
uint8_t v_compile_4515_ = stack[3].m_num;
uint8_t v_logCompileErrors_4516_ = stack[4].m_num;
lean_object* v_a_4517_ = stack[5].m_obj;
lean_object* v_a_4518_ = stack[6].m_obj;
lean_object* v_a_4519_ = stack[7].m_obj;
lean_object* v_a_4520_ = stack[8].m_obj;
lean_object* v_res_4526_;
v_res_4526_ = l_Lean_Meta_mkAuxDefinitionFor(v_name_4512_, v_value_4513_, v_zetaDelta_4514_, v_compile_4515_, v_logCompileErrors_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
stack->m_obj
 = v_res_4526_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* v_name_4527_, lean_object* v_value_4528_, lean_object* v_zetaDelta_4529_, lean_object* v_compile_4530_, lean_object* v_logCompileErrors_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_){
_start:
{
uint8_t v_zetaDelta_boxed_4537_; uint8_t v_compile_boxed_4538_; uint8_t v_logCompileErrors_boxed_4539_; lean_object* v_res_4540_; 
v_zetaDelta_boxed_4537_ = lean_unbox(v_zetaDelta_4529_);
v_compile_boxed_4538_ = lean_unbox(v_compile_4530_);
v_logCompileErrors_boxed_4539_ = lean_unbox(v_logCompileErrors_4531_);
v_res_4540_ = l_Lean_Meta_mkAuxDefinitionFor(v_name_4527_, v_value_4528_, v_zetaDelta_boxed_4537_, v_compile_boxed_4538_, v_logCompileErrors_boxed_4539_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_);
lean_dec(v_a_4535_);
lean_dec_ref(v_a_4534_);
lean_dec(v_a_4533_);
lean_dec_ref(v_a_4532_);
return v_res_4540_;
}
}
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* v_type_4541_, lean_object* v_value_4542_, uint8_t v_zetaDelta_4543_, lean_object* v_kind_x3f_4544_, uint8_t v_cache_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4541_, v_value_4542_, v_zetaDelta_4543_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v_a_4552_; lean_object* v_levelParams_4553_; lean_object* v_type_4554_; lean_object* v_value_4555_; lean_object* v_levelArgs_4556_; lean_object* v_exprArgs_4557_; lean_object* v___x_4558_; uint8_t v___x_4559_; lean_object* v___x_4560_; 
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
lean_dec_ref_known(v___x_4551_, 1);
v_levelParams_4553_ = lean_ctor_get(v_a_4552_, 0);
lean_inc_ref(v_levelParams_4553_);
v_type_4554_ = lean_ctor_get(v_a_4552_, 1);
lean_inc_ref(v_type_4554_);
v_value_4555_ = lean_ctor_get(v_a_4552_, 2);
lean_inc_ref(v_value_4555_);
v_levelArgs_4556_ = lean_ctor_get(v_a_4552_, 3);
lean_inc_ref(v_levelArgs_4556_);
v_exprArgs_4557_ = lean_ctor_get(v_a_4552_, 4);
lean_inc_ref(v_exprArgs_4557_);
lean_dec(v_a_4552_);
v___x_4558_ = lean_array_to_list(v_levelParams_4553_);
v___x_4559_ = 0;
v___x_4560_ = l_Lean_Meta_mkAuxLemma(v___x_4558_, v_type_4554_, v_value_4555_, v_kind_x3f_4544_, v_cache_4545_, v___x_4559_, v___x_4559_, v___x_4559_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4571_; 
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4563_ = v___x_4560_;
v_isShared_4564_ = v_isSharedCheck_4571_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4560_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4571_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4569_; 
v___x_4565_ = lean_array_to_list(v_levelArgs_4556_);
v___x_4566_ = l_Lean_mkConst(v_a_4561_, v___x_4565_);
v___x_4567_ = l_Lean_mkAppN(v___x_4566_, v_exprArgs_4557_);
lean_dec_ref(v_exprArgs_4557_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v___x_4567_);
v___x_4569_ = v___x_4563_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec_ref(v_exprArgs_4557_);
lean_dec_ref(v_levelArgs_4556_);
v_a_4572_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4560_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4560_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
lean_dec(v_kind_x3f_4544_);
v_a_4580_ = lean_ctor_get(v___x_4551_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v___x_4551_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4551_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4585_; 
if (v_isShared_4583_ == 0)
{
v___x_4585_ = v___x_4582_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkAuxTheorem_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_4541_ = stack[0].m_obj;
lean_object* v_value_4542_ = stack[1].m_obj;
uint8_t v_zetaDelta_4543_ = stack[2].m_num;
lean_object* v_kind_x3f_4544_ = stack[3].m_obj;
uint8_t v_cache_4545_ = stack[4].m_num;
lean_object* v_a_4546_ = stack[5].m_obj;
lean_object* v_a_4547_ = stack[6].m_obj;
lean_object* v_a_4548_ = stack[7].m_obj;
lean_object* v_a_4549_ = stack[8].m_obj;
lean_object* v_res_4588_;
v_res_4588_ = l_Lean_Meta_mkAuxTheorem(v_type_4541_, v_value_4542_, v_zetaDelta_4543_, v_kind_x3f_4544_, v_cache_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_);
stack->m_obj
 = v_res_4588_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* v_type_4589_, lean_object* v_value_4590_, lean_object* v_zetaDelta_4591_, lean_object* v_kind_x3f_4592_, lean_object* v_cache_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_){
_start:
{
uint8_t v_zetaDelta_boxed_4599_; uint8_t v_cache_boxed_4600_; lean_object* v_res_4601_; 
v_zetaDelta_boxed_4599_ = lean_unbox(v_zetaDelta_4591_);
v_cache_boxed_4600_ = lean_unbox(v_cache_4593_);
v_res_4601_ = l_Lean_Meta_mkAuxTheorem(v_type_4589_, v_value_4590_, v_zetaDelta_boxed_4599_, v_kind_x3f_4592_, v_cache_boxed_4600_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_);
lean_dec(v_a_4597_);
lean_dec_ref(v_a_4596_);
lean_dec(v_a_4595_);
lean_dec_ref(v_a_4594_);
return v_res_4601_;
}
}
lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4657_; uint8_t v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4657_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_4658_ = 0;
v___x_4659_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_));
v___x_4660_ = l_Lean_registerTraceClass(v___x_4657_, v___x_4658_, v___x_4659_);
return v___x_4660_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4661_;
v_res_4661_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4661_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(lean_object* v_a_4662_){
_start:
{
lean_object* v_res_4663_; 
v_res_4663_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
return v_res_4663_;
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
