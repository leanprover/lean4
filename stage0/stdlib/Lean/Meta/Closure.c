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
static const lean_closure_object l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___x_154_; lean_object* v_nextLevelIdx_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_visitedLevel_159_; lean_object* v_visitedExpr_160_; lean_object* v_levelParams_161_; lean_object* v_nextLevelIdx_162_; lean_object* v_levelArgs_163_; lean_object* v_newLocalDecls_164_; lean_object* v_newLocalDeclsForMVars_165_; lean_object* v_newLetDecls_166_; lean_object* v_nextExprIdx_167_; lean_object* v_exprMVarArgs_168_; lean_object* v_exprFVarArgs_169_; lean_object* v_toProcess_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_184_; 
v___x_154_ = lean_st_ref_get(v_a_152_);
v_nextLevelIdx_155_ = lean_ctor_get(v___x_154_, 3);
lean_inc(v_nextLevelIdx_155_);
lean_dec(v___x_154_);
v___x_156_ = ((lean_object*)(l_Lean_Meta_Closure_mkNewLevelParam___redArg___closed__1));
v___x_157_ = lean_name_append_index_after(v___x_156_, v_nextLevelIdx_155_);
v___x_158_ = lean_st_ref_take(v_a_152_);
v_visitedLevel_159_ = lean_ctor_get(v___x_158_, 0);
v_visitedExpr_160_ = lean_ctor_get(v___x_158_, 1);
v_levelParams_161_ = lean_ctor_get(v___x_158_, 2);
v_nextLevelIdx_162_ = lean_ctor_get(v___x_158_, 3);
v_levelArgs_163_ = lean_ctor_get(v___x_158_, 4);
v_newLocalDecls_164_ = lean_ctor_get(v___x_158_, 5);
v_newLocalDeclsForMVars_165_ = lean_ctor_get(v___x_158_, 6);
v_newLetDecls_166_ = lean_ctor_get(v___x_158_, 7);
v_nextExprIdx_167_ = lean_ctor_get(v___x_158_, 8);
v_exprMVarArgs_168_ = lean_ctor_get(v___x_158_, 9);
v_exprFVarArgs_169_ = lean_ctor_get(v___x_158_, 10);
v_toProcess_170_ = lean_ctor_get(v___x_158_, 11);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_184_ == 0)
{
v___x_172_ = v___x_158_;
v_isShared_173_ = v_isSharedCheck_184_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_toProcess_170_);
lean_inc(v_exprFVarArgs_169_);
lean_inc(v_exprMVarArgs_168_);
lean_inc(v_nextExprIdx_167_);
lean_inc(v_newLetDecls_166_);
lean_inc(v_newLocalDeclsForMVars_165_);
lean_inc(v_newLocalDecls_164_);
lean_inc(v_levelArgs_163_);
lean_inc(v_nextLevelIdx_162_);
lean_inc(v_levelParams_161_);
lean_inc(v_visitedExpr_160_);
lean_inc(v_visitedLevel_159_);
lean_dec(v___x_158_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_184_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
lean_inc(v___x_157_);
v___x_174_ = lean_array_push(v_levelParams_161_, v___x_157_);
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_add(v_nextLevelIdx_162_, v___x_175_);
lean_dec(v_nextLevelIdx_162_);
v___x_177_ = lean_array_push(v_levelArgs_163_, v_u_151_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 4, v___x_177_);
lean_ctor_set(v___x_172_, 3, v___x_176_);
lean_ctor_set(v___x_172_, 2, v___x_174_);
v___x_179_ = v___x_172_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_visitedLevel_159_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_visitedExpr_160_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_183_, 3, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_183_, 4, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_183_, 5, v_newLocalDecls_164_);
lean_ctor_set(v_reuseFailAlloc_183_, 6, v_newLocalDeclsForMVars_165_);
lean_ctor_set(v_reuseFailAlloc_183_, 7, v_newLetDecls_166_);
lean_ctor_set(v_reuseFailAlloc_183_, 8, v_nextExprIdx_167_);
lean_ctor_set(v_reuseFailAlloc_183_, 9, v_exprMVarArgs_168_);
lean_ctor_set(v_reuseFailAlloc_183_, 10, v_exprFVarArgs_169_);
lean_ctor_set(v_reuseFailAlloc_183_, 11, v_toProcess_170_);
v___x_179_ = v_reuseFailAlloc_183_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_st_ref_put(v_a_152_, v___x_179_);
v___x_181_ = l_Lean_mkLevelParam(v___x_157_);
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
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_nbuckets_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_285_ = lean_array_get_size(v_data_284_);
v___x_286_ = lean_unsigned_to_nat(2u);
v_nbuckets_287_ = lean_nat_mul(v___x_285_, v___x_286_);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_box(0);
v___x_290_ = lean_mk_array(v_nbuckets_287_, v___x_289_);
v___x_291_ = lean_array_propagate_mark(v_data_284_, v___x_290_);
v___x_292_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v___x_288_, v_data_284_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(lean_object* v_a_293_, lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
uint8_t v___x_295_; 
v___x_295_ = 0;
return v___x_295_;
}
else
{
lean_object* v_key_296_; lean_object* v_tail_297_; uint8_t v___x_298_; 
v_key_296_ = lean_ctor_get(v_x_294_, 0);
v_tail_297_ = lean_ctor_get(v_x_294_, 2);
v___x_298_ = lean_level_eq(v_key_296_, v_a_293_);
if (v___x_298_ == 0)
{
v_x_294_ = v_tail_297_;
goto _start;
}
else
{
return v___x_298_;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg(lean_object* v_x_370_, lean_object* v_a_371_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___redArg___boxed(lean_object* v_x_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_584_, v_a_585_);
lean_dec(v_a_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux(lean_object* v_x_588_, uint8_t v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_x_588_, v_a_590_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevelAux___boxed(lean_object* v_x_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
uint8_t v_a_boxed_605_; lean_object* v_res_606_; 
v_a_boxed_605_ = lean_unbox(v_a_598_);
v_res_606_ = l_Lean_Meta_Closure_collectLevelAux(v_x_597_, v_a_boxed_605_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(lean_object* v_00_u03b2_607_, lean_object* v_m_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_m_608_, v_a_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___boxed(lean_object* v_00_u03b2_611_, lean_object* v_m_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1(v_00_u03b2_611_, v_m_612_, v_a_613_);
lean_dec(v_a_613_);
lean_dec_ref(v_m_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2(lean_object* v_00_u03b2_615_, lean_object* v_m_616_, lean_object* v_a_617_, lean_object* v_b_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_m_616_, v_a_617_, v_b_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(lean_object* v_00_u03b2_620_, lean_object* v_a_621_, lean_object* v_x_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___redArg(v_a_621_, v_x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1___boxed(lean_object* v_00_u03b2_624_, lean_object* v_a_625_, lean_object* v_x_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1_spec__1(v_00_u03b2_624_, v_a_625_, v_x_626_);
lean_dec(v_x_626_);
lean_dec(v_a_625_);
return v_res_627_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(lean_object* v_00_u03b2_628_, lean_object* v_a_629_, lean_object* v_x_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___redArg(v_a_629_, v_x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3___boxed(lean_object* v_00_u03b2_632_, lean_object* v_a_633_, lean_object* v_x_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__3(v_00_u03b2_632_, v_a_633_, v_x_634_);
lean_dec(v_x_634_);
lean_dec(v_a_633_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4(lean_object* v_00_u03b2_637_, lean_object* v_data_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4___redArg(v_data_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5(lean_object* v_00_u03b2_640_, lean_object* v_a_641_, lean_object* v_b_642_, lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__5___redArg(v_a_641_, v_b_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_645_, lean_object* v_i_646_, lean_object* v_source_647_, lean_object* v_target_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5___redArg(v_i_646_, v_source_647_, v_target_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2_spec__4_spec__5_spec__6___redArg(v_x_651_, v_x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg(lean_object* v_u_654_, lean_object* v_a_655_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = l_Lean_Level_hasMVar(v_u_654_);
if (v___x_700_ == 0)
{
uint8_t v___x_701_; 
v___x_701_ = l_Lean_Level_hasParam(v_u_654_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v_u_654_);
return v___x_702_;
}
else
{
goto v___jp_657_;
}
}
else
{
goto v___jp_657_;
}
v___jp_657_:
{
lean_object* v___x_658_; lean_object* v_visitedLevel_659_; lean_object* v___x_660_; 
v___x_658_ = lean_st_ref_get(v_a_655_);
v_visitedLevel_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc_ref(v_visitedLevel_659_);
lean_dec(v___x_658_);
v___x_660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectLevelAux_spec__1___redArg(v_visitedLevel_659_, v_u_654_);
lean_dec_ref(v_visitedLevel_659_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v___x_661_; 
lean_inc(v_u_654_);
v___x_661_ = l_Lean_Meta_Closure_collectLevelAux___redArg(v_u_654_, v_a_655_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_691_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_691_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_691_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_691_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v_visitedLevel_667_; lean_object* v_visitedExpr_668_; lean_object* v_levelParams_669_; lean_object* v_nextLevelIdx_670_; lean_object* v_levelArgs_671_; lean_object* v_newLocalDecls_672_; lean_object* v_newLocalDeclsForMVars_673_; lean_object* v_newLetDecls_674_; lean_object* v_nextExprIdx_675_; lean_object* v_exprMVarArgs_676_; lean_object* v_exprFVarArgs_677_; lean_object* v_toProcess_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_690_; 
v___x_666_ = lean_st_ref_take(v_a_655_);
v_visitedLevel_667_ = lean_ctor_get(v___x_666_, 0);
v_visitedExpr_668_ = lean_ctor_get(v___x_666_, 1);
v_levelParams_669_ = lean_ctor_get(v___x_666_, 2);
v_nextLevelIdx_670_ = lean_ctor_get(v___x_666_, 3);
v_levelArgs_671_ = lean_ctor_get(v___x_666_, 4);
v_newLocalDecls_672_ = lean_ctor_get(v___x_666_, 5);
v_newLocalDeclsForMVars_673_ = lean_ctor_get(v___x_666_, 6);
v_newLetDecls_674_ = lean_ctor_get(v___x_666_, 7);
v_nextExprIdx_675_ = lean_ctor_get(v___x_666_, 8);
v_exprMVarArgs_676_ = lean_ctor_get(v___x_666_, 9);
v_exprFVarArgs_677_ = lean_ctor_get(v___x_666_, 10);
v_toProcess_678_ = lean_ctor_get(v___x_666_, 11);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_690_ == 0)
{
v___x_680_ = v___x_666_;
v_isShared_681_ = v_isSharedCheck_690_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_toProcess_678_);
lean_inc(v_exprFVarArgs_677_);
lean_inc(v_exprMVarArgs_676_);
lean_inc(v_nextExprIdx_675_);
lean_inc(v_newLetDecls_674_);
lean_inc(v_newLocalDeclsForMVars_673_);
lean_inc(v_newLocalDecls_672_);
lean_inc(v_levelArgs_671_);
lean_inc(v_nextLevelIdx_670_);
lean_inc(v_levelParams_669_);
lean_inc(v_visitedExpr_668_);
lean_inc(v_visitedLevel_667_);
lean_dec(v___x_666_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_690_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
lean_inc(v_a_662_);
v___x_682_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectLevelAux_spec__2___redArg(v_visitedLevel_667_, v_u_654_, v_a_662_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_visitedExpr_668_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_levelParams_669_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v_nextLevelIdx_670_);
lean_ctor_set(v_reuseFailAlloc_689_, 4, v_levelArgs_671_);
lean_ctor_set(v_reuseFailAlloc_689_, 5, v_newLocalDecls_672_);
lean_ctor_set(v_reuseFailAlloc_689_, 6, v_newLocalDeclsForMVars_673_);
lean_ctor_set(v_reuseFailAlloc_689_, 7, v_newLetDecls_674_);
lean_ctor_set(v_reuseFailAlloc_689_, 8, v_nextExprIdx_675_);
lean_ctor_set(v_reuseFailAlloc_689_, 9, v_exprMVarArgs_676_);
lean_ctor_set(v_reuseFailAlloc_689_, 10, v_exprFVarArgs_677_);
lean_ctor_set(v_reuseFailAlloc_689_, 11, v_toProcess_678_);
v___x_684_ = v_reuseFailAlloc_689_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = lean_st_ref_put(v_a_655_, v___x_684_);
if (v_isShared_665_ == 0)
{
v___x_687_ = v___x_664_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_662_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
else
{
lean_dec(v_u_654_);
return v___x_661_;
}
}
else
{
lean_object* v_val_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec(v_u_654_);
v_val_692_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_660_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_val_692_);
lean_dec(v___x_660_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set_tag(v___x_694_, 0);
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_val_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___redArg___boxed(lean_object* v_u_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_703_, v_a_704_);
lean_dec(v_a_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel(lean_object* v_u_707_, uint8_t v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_707_, v_a_709_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectLevel___boxed(lean_object* v_u_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
uint8_t v_a_boxed_724_; lean_object* v_res_725_; 
v_a_boxed_724_ = lean_unbox(v_a_717_);
v_res_725_ = l_Lean_Meta_Closure_collectLevel(v_u_716_, v_a_boxed_724_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(lean_object* v_e_726_, lean_object* v___y_727_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = l_Lean_Expr_hasMVar(v_e_726_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v_e_726_);
return v___x_730_;
}
else
{
lean_object* v___x_731_; lean_object* v_mctx_732_; lean_object* v___x_733_; lean_object* v_fst_734_; lean_object* v_snd_735_; lean_object* v___x_736_; lean_object* v_cache_737_; lean_object* v_zetaDeltaFVarIds_738_; lean_object* v_postponed_739_; lean_object* v_diag_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_749_; 
v___x_731_ = lean_st_ref_get(v___y_727_);
v_mctx_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc_ref(v_mctx_732_);
lean_dec(v___x_731_);
v___x_733_ = l_Lean_instantiateMVarsCore(v_mctx_732_, v_e_726_);
v_fst_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_fst_734_);
v_snd_735_ = lean_ctor_get(v___x_733_, 1);
lean_inc(v_snd_735_);
lean_dec_ref(v___x_733_);
v___x_736_ = lean_st_ref_take(v___y_727_);
v_cache_737_ = lean_ctor_get(v___x_736_, 1);
v_zetaDeltaFVarIds_738_ = lean_ctor_get(v___x_736_, 2);
v_postponed_739_ = lean_ctor_get(v___x_736_, 3);
v_diag_740_ = lean_ctor_get(v___x_736_, 4);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v___x_736_, 0);
lean_dec(v_unused_750_);
v___x_742_ = v___x_736_;
v_isShared_743_ = v_isSharedCheck_749_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_diag_740_);
lean_inc(v_postponed_739_);
lean_inc(v_zetaDeltaFVarIds_738_);
lean_inc(v_cache_737_);
lean_dec(v___x_736_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_749_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v_snd_735_);
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_snd_735_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_cache_737_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_zetaDeltaFVarIds_738_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_postponed_739_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_diag_740_);
v___x_745_ = v_reuseFailAlloc_748_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_st_ref_put(v___y_727_, v___x_745_);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v_fst_734_);
return v___x_747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg___boxed(lean_object* v_e_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_751_, v___y_752_);
lean_dec(v___y_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(lean_object* v_e_755_, uint8_t v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_755_, v___y_759_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___boxed(lean_object* v_e_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
uint8_t v___y_2276__boxed_772_; lean_object* v_res_773_; 
v___y_2276__boxed_772_ = lean_unbox(v___y_765_);
v_res_773_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0(v_e_764_, v___y_2276__boxed_772_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess(lean_object* v_e_774_, uint8_t v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_instantiateMVars___at___00Lean_Meta_Closure_preprocess_spec__0___redArg(v_e_774_, v_a_778_);
if (v_a_775_ == 0)
{
lean_object* v_a_783_; uint8_t v___x_784_; lean_object* v___x_785_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc_n(v_a_783_, 2);
lean_dec_ref(v___x_782_);
v___x_784_ = 0;
v___x_785_ = l_Lean_Meta_check(v_a_783_, v___x_784_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v___x_785_, 0);
lean_dec(v_unused_793_);
v___x_787_ = v___x_785_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_dec(v___x_785_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_a_783_);
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_783_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v_a_783_);
v_a_794_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_785_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_785_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_preprocess___boxed(lean_object* v_e_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
uint8_t v_a_boxed_810_; lean_object* v_res_811_; 
v_a_boxed_810_ = lean_unbox(v_a_803_);
v_res_811_ = l_Lean_Meta_Closure_preprocess(v_e_802_, v_a_boxed_810_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg(lean_object* v_a_815_){
_start:
{
lean_object* v___x_817_; lean_object* v_nextExprIdx_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v_visitedLevel_822_; lean_object* v_visitedExpr_823_; lean_object* v_levelParams_824_; lean_object* v_nextLevelIdx_825_; lean_object* v_levelArgs_826_; lean_object* v_newLocalDecls_827_; lean_object* v_newLocalDeclsForMVars_828_; lean_object* v_newLetDecls_829_; lean_object* v_nextExprIdx_830_; lean_object* v_exprMVarArgs_831_; lean_object* v_exprFVarArgs_832_; lean_object* v_toProcess_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_844_; 
v___x_817_ = lean_st_ref_get(v_a_815_);
v_nextExprIdx_818_ = lean_ctor_get(v___x_817_, 8);
lean_inc(v_nextExprIdx_818_);
lean_dec(v___x_817_);
v___x_819_ = ((lean_object*)(l_Lean_Meta_Closure_mkNextUserName___redArg___closed__1));
v___x_820_ = lean_name_append_index_after(v___x_819_, v_nextExprIdx_818_);
v___x_821_ = lean_st_ref_take(v_a_815_);
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
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_844_ == 0)
{
v___x_835_ = v___x_821_;
v_isShared_836_ = v_isSharedCheck_844_;
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
v_isShared_836_ = v_isSharedCheck_844_;
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
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_visitedLevel_822_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_visitedExpr_823_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v_levelParams_824_);
lean_ctor_set(v_reuseFailAlloc_843_, 3, v_nextLevelIdx_825_);
lean_ctor_set(v_reuseFailAlloc_843_, 4, v_levelArgs_826_);
lean_ctor_set(v_reuseFailAlloc_843_, 5, v_newLocalDecls_827_);
lean_ctor_set(v_reuseFailAlloc_843_, 6, v_newLocalDeclsForMVars_828_);
lean_ctor_set(v_reuseFailAlloc_843_, 7, v_newLetDecls_829_);
lean_ctor_set(v_reuseFailAlloc_843_, 8, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_843_, 9, v_exprMVarArgs_831_);
lean_ctor_set(v_reuseFailAlloc_843_, 10, v_exprFVarArgs_832_);
lean_ctor_set(v_reuseFailAlloc_843_, 11, v_toProcess_833_);
v___x_840_ = v_reuseFailAlloc_843_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_st_ref_put(v_a_815_, v___x_840_);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_820_);
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___redArg___boxed(lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_845_);
lean_dec(v_a_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName(uint8_t v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_849_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkNextUserName___boxed(lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
uint8_t v_a_boxed_863_; lean_object* v_res_864_; 
v_a_boxed_863_ = lean_unbox(v_a_856_);
v_res_864_ = l_Lean_Meta_Closure_mkNextUserName(v_a_boxed_863_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg(lean_object* v_elem_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; lean_object* v_visitedLevel_869_; lean_object* v_visitedExpr_870_; lean_object* v_levelParams_871_; lean_object* v_nextLevelIdx_872_; lean_object* v_levelArgs_873_; lean_object* v_newLocalDecls_874_; lean_object* v_newLocalDeclsForMVars_875_; lean_object* v_newLetDecls_876_; lean_object* v_nextExprIdx_877_; lean_object* v_exprMVarArgs_878_; lean_object* v_exprFVarArgs_879_; lean_object* v_toProcess_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_891_; 
v___x_868_ = lean_st_ref_take(v_a_866_);
v_visitedLevel_869_ = lean_ctor_get(v___x_868_, 0);
v_visitedExpr_870_ = lean_ctor_get(v___x_868_, 1);
v_levelParams_871_ = lean_ctor_get(v___x_868_, 2);
v_nextLevelIdx_872_ = lean_ctor_get(v___x_868_, 3);
v_levelArgs_873_ = lean_ctor_get(v___x_868_, 4);
v_newLocalDecls_874_ = lean_ctor_get(v___x_868_, 5);
v_newLocalDeclsForMVars_875_ = lean_ctor_get(v___x_868_, 6);
v_newLetDecls_876_ = lean_ctor_get(v___x_868_, 7);
v_nextExprIdx_877_ = lean_ctor_get(v___x_868_, 8);
v_exprMVarArgs_878_ = lean_ctor_get(v___x_868_, 9);
v_exprFVarArgs_879_ = lean_ctor_get(v___x_868_, 10);
v_toProcess_880_ = lean_ctor_get(v___x_868_, 11);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_891_ == 0)
{
v___x_882_ = v___x_868_;
v_isShared_883_ = v_isSharedCheck_891_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_toProcess_880_);
lean_inc(v_exprFVarArgs_879_);
lean_inc(v_exprMVarArgs_878_);
lean_inc(v_nextExprIdx_877_);
lean_inc(v_newLetDecls_876_);
lean_inc(v_newLocalDeclsForMVars_875_);
lean_inc(v_newLocalDecls_874_);
lean_inc(v_levelArgs_873_);
lean_inc(v_nextLevelIdx_872_);
lean_inc(v_levelParams_871_);
lean_inc(v_visitedExpr_870_);
lean_inc(v_visitedLevel_869_);
lean_dec(v___x_868_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_891_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_884_ = lean_box(0);
v___x_885_ = lean_array_push(v_toProcess_880_, v_elem_865_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 11, v___x_885_);
v___x_887_ = v___x_882_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_visitedLevel_869_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_visitedExpr_870_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_levelParams_871_);
lean_ctor_set(v_reuseFailAlloc_890_, 3, v_nextLevelIdx_872_);
lean_ctor_set(v_reuseFailAlloc_890_, 4, v_levelArgs_873_);
lean_ctor_set(v_reuseFailAlloc_890_, 5, v_newLocalDecls_874_);
lean_ctor_set(v_reuseFailAlloc_890_, 6, v_newLocalDeclsForMVars_875_);
lean_ctor_set(v_reuseFailAlloc_890_, 7, v_newLetDecls_876_);
lean_ctor_set(v_reuseFailAlloc_890_, 8, v_nextExprIdx_877_);
lean_ctor_set(v_reuseFailAlloc_890_, 9, v_exprMVarArgs_878_);
lean_ctor_set(v_reuseFailAlloc_890_, 10, v_exprFVarArgs_879_);
lean_ctor_set(v_reuseFailAlloc_890_, 11, v___x_885_);
v___x_887_ = v_reuseFailAlloc_890_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_st_ref_put(v_a_866_, v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_884_);
return v___x_889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___redArg___boxed(lean_object* v_elem_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_892_, v_a_893_);
lean_dec(v_a_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess(lean_object* v_elem_896_, uint8_t v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Meta_Closure_pushToProcess___redArg(v_elem_896_, v_a_898_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushToProcess___boxed(lean_object* v_elem_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
uint8_t v_a_boxed_913_; lean_object* v_res_914_; 
v_a_boxed_913_ = lean_unbox(v_a_906_);
v_res_914_ = l_Lean_Meta_Closure_pushToProcess(v_elem_905_, v_a_boxed_913_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(lean_object* v_mvarId_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; lean_object* v_mctx_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_918_ = lean_st_ref_get(v___y_916_);
v_mctx_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc_ref(v_mctx_919_);
lean_dec(v___x_918_);
v___x_920_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_919_, v_mvarId_915_);
lean_dec_ref(v_mctx_919_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg___boxed(lean_object* v_mvarId_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec(v_mvarId_922_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(lean_object* v_mvarId_926_, uint8_t v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_926_, v___y_930_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___boxed(lean_object* v_mvarId_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
uint8_t v___y_18037__boxed_943_; lean_object* v_res_944_; 
v___y_18037__boxed_943_ = lean_unbox(v___y_936_);
v_res_944_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4(v_mvarId_935_, v___y_18037__boxed_943_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v_mvarId_935_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(lean_object* v_k_945_, uint8_t v___y_946_, lean_object* v___y_947_, lean_object* v_b_948_, lean_object* v_c_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_box(v___y_946_);
lean_inc(v___y_953_);
lean_inc_ref(v___y_952_);
lean_inc(v___y_951_);
lean_inc_ref(v___y_950_);
lean_inc(v___y_947_);
v___x_956_ = lean_apply_9(v_k_945_, v_b_948_, v_c_949_, v___x_955_, v___y_947_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, lean_box(0));
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed(lean_object* v_k_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v_b_960_, lean_object* v_c_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
uint8_t v___y_18060__boxed_967_; lean_object* v_res_968_; 
v___y_18060__boxed_967_ = lean_unbox(v___y_958_);
v_res_968_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0(v_k_957_, v___y_18060__boxed_967_, v___y_959_, v_b_960_, v_c_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_959_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(lean_object* v_type_969_, lean_object* v_maxFVars_x3f_970_, lean_object* v_k_971_, uint8_t v_cleanupAnnotations_972_, uint8_t v_whnfType_973_, uint8_t v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; lean_object* v___f_982_; lean_object* v___x_983_; 
v___x_981_ = lean_box(v___y_974_);
lean_inc(v___y_975_);
v___f_982_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_982_, 0, v_k_971_);
lean_closure_set(v___f_982_, 1, v___x_981_);
lean_closure_set(v___f_982_, 2, v___y_975_);
v___x_983_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_969_, v_maxFVars_x3f_970_, v___f_982_, v_cleanupAnnotations_972_, v_whnfType_973_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_983_) == 0)
{
return v___x_983_;
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg___boxed(lean_object* v_type_992_, lean_object* v_maxFVars_x3f_993_, lean_object* v_k_994_, lean_object* v_cleanupAnnotations_995_, lean_object* v_whnfType_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1004_; uint8_t v_whnfType_boxed_1005_; uint8_t v___y_18085__boxed_1006_; lean_object* v_res_1007_; 
v_cleanupAnnotations_boxed_1004_ = lean_unbox(v_cleanupAnnotations_995_);
v_whnfType_boxed_1005_ = lean_unbox(v_whnfType_996_);
v___y_18085__boxed_1006_ = lean_unbox(v___y_997_);
v_res_1007_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_992_, v_maxFVars_x3f_993_, v_k_994_, v_cleanupAnnotations_boxed_1004_, v_whnfType_boxed_1005_, v___y_18085__boxed_1006_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(lean_object* v_00_u03b1_1008_, lean_object* v_type_1009_, lean_object* v_maxFVars_x3f_1010_, lean_object* v_k_1011_, uint8_t v_cleanupAnnotations_1012_, uint8_t v_whnfType_1013_, uint8_t v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1009_, v_maxFVars_x3f_1010_, v_k_1011_, v_cleanupAnnotations_1012_, v_whnfType_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___boxed(lean_object* v_00_u03b1_1022_, lean_object* v_type_1023_, lean_object* v_maxFVars_x3f_1024_, lean_object* v_k_1025_, lean_object* v_cleanupAnnotations_1026_, lean_object* v_whnfType_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1035_; uint8_t v_whnfType_boxed_1036_; uint8_t v___y_18129__boxed_1037_; lean_object* v_res_1038_; 
v_cleanupAnnotations_boxed_1035_ = lean_unbox(v_cleanupAnnotations_1026_);
v_whnfType_boxed_1036_ = lean_unbox(v_whnfType_1027_);
v___y_18129__boxed_1037_ = lean_unbox(v___y_1028_);
v_res_1038_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5(v_00_u03b1_1022_, v_type_1023_, v_maxFVars_x3f_1024_, v_k_1025_, v_cleanupAnnotations_boxed_1035_, v_whnfType_boxed_1036_, v___y_18129__boxed_1037_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(lean_object* v_a_1039_, lean_object* v_x_1040_){
_start:
{
if (lean_obj_tag(v_x_1040_) == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_box(0);
return v___x_1041_;
}
else
{
lean_object* v_key_1042_; lean_object* v_value_1043_; lean_object* v_tail_1044_; uint8_t v___x_1045_; 
v_key_1042_ = lean_ctor_get(v_x_1040_, 0);
v_value_1043_ = lean_ctor_get(v_x_1040_, 1);
v_tail_1044_ = lean_ctor_get(v_x_1040_, 2);
v___x_1045_ = l_Lean_ExprStructEq_beq(v_key_1042_, v_a_1039_);
if (v___x_1045_ == 0)
{
v_x_1040_ = v_tail_1044_;
goto _start;
}
else
{
lean_object* v___x_1047_; 
lean_inc(v_value_1043_);
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v_value_1043_);
return v___x_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1048_, v_x_1049_);
lean_dec(v_x_1049_);
lean_dec_ref(v_a_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(lean_object* v_m_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_buckets_1053_; lean_object* v___x_1054_; uint64_t v___x_1055_; uint64_t v___x_1056_; uint64_t v___x_1057_; uint64_t v_fold_1058_; uint64_t v___x_1059_; uint64_t v___x_1060_; uint64_t v___x_1061_; size_t v___x_1062_; size_t v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_buckets_1053_ = lean_ctor_get(v_m_1051_, 1);
v___x_1054_ = lean_array_get_size(v_buckets_1053_);
v___x_1055_ = l_Lean_ExprStructEq_hash(v_a_1052_);
v___x_1056_ = 32ULL;
v___x_1057_ = lean_uint64_shift_right(v___x_1055_, v___x_1056_);
v_fold_1058_ = lean_uint64_xor(v___x_1055_, v___x_1057_);
v___x_1059_ = 16ULL;
v___x_1060_ = lean_uint64_shift_right(v_fold_1058_, v___x_1059_);
v___x_1061_ = lean_uint64_xor(v_fold_1058_, v___x_1060_);
v___x_1062_ = lean_uint64_to_usize(v___x_1061_);
v___x_1063_ = lean_usize_of_nat(v___x_1054_);
v___x_1064_ = ((size_t)1ULL);
v___x_1065_ = lean_usize_sub(v___x_1063_, v___x_1064_);
v___x_1066_ = lean_usize_land(v___x_1062_, v___x_1065_);
v___x_1067_ = lean_array_uget_borrowed(v_buckets_1053_, v___x_1066_);
v___x_1068_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1052_, v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg___boxed(lean_object* v_m_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1069_, v_a_1070_);
lean_dec_ref(v_a_1070_);
lean_dec_ref(v_m_1069_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(lean_object* v_x_1072_, lean_object* v_x_1073_, lean_object* v___y_1074_){
_start:
{
if (lean_obj_tag(v_x_1072_) == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = l_List_reverse___redArg(v_x_1073_);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
else
{
lean_object* v_head_1078_; lean_object* v_tail_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1097_; 
v_head_1078_ = lean_ctor_get(v_x_1072_, 0);
v_tail_1079_ = lean_ctor_get(v_x_1072_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1081_ = v_x_1072_;
v_isShared_1082_ = v_isSharedCheck_1097_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_tail_1079_);
lean_inc(v_head_1078_);
lean_dec(v_x_1072_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1097_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Meta_Closure_collectLevel___redArg(v_head_1078_, v___y_1074_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 1, v_x_1073_);
lean_ctor_set(v___x_1081_, 0, v_a_1084_);
v___x_1086_ = v___x_1081_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1084_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_x_1073_);
v___x_1086_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
v_x_1072_ = v_tail_1079_;
v_x_1073_ = v___x_1086_;
goto _start;
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_del_object(v___x_1081_);
lean_dec(v_tail_1079_);
lean_dec(v_x_1073_);
v_a_1089_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1083_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1083_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg___boxed(lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1098_, v_x_1099_, v___y_1100_);
lean_dec(v___y_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v_ngen_1106_; lean_object* v_namePrefix_1107_; lean_object* v_idx_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1137_; 
v___x_1105_ = lean_st_ref_get(v___y_1103_);
v_ngen_1106_ = lean_ctor_get(v___x_1105_, 2);
lean_inc_ref(v_ngen_1106_);
lean_dec(v___x_1105_);
v_namePrefix_1107_ = lean_ctor_get(v_ngen_1106_, 0);
v_idx_1108_ = lean_ctor_get(v_ngen_1106_, 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_ngen_1106_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1110_ = v_ngen_1106_;
v_isShared_1111_ = v_isSharedCheck_1137_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_idx_1108_);
lean_inc(v_namePrefix_1107_);
lean_dec(v_ngen_1106_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1137_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v_r_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
lean_inc(v_idx_1108_);
lean_inc(v_namePrefix_1107_);
v_r_1112_ = l_Lean_Name_num___override(v_namePrefix_1107_, v_idx_1108_);
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_add(v_idx_1108_, v___x_1113_);
lean_dec(v_idx_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 1, v___x_1114_);
v___x_1116_ = v___x_1110_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_namePrefix_1107_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; lean_object* v_env_1118_; lean_object* v_nextMacroScope_1119_; lean_object* v_auxDeclNGen_1120_; lean_object* v_traceState_1121_; lean_object* v_cache_1122_; lean_object* v_messages_1123_; lean_object* v_infoState_1124_; lean_object* v_snapshotTasks_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1134_; 
v___x_1117_ = lean_st_ref_take(v___y_1103_);
v_env_1118_ = lean_ctor_get(v___x_1117_, 0);
v_nextMacroScope_1119_ = lean_ctor_get(v___x_1117_, 1);
v_auxDeclNGen_1120_ = lean_ctor_get(v___x_1117_, 3);
v_traceState_1121_ = lean_ctor_get(v___x_1117_, 4);
v_cache_1122_ = lean_ctor_get(v___x_1117_, 5);
v_messages_1123_ = lean_ctor_get(v___x_1117_, 6);
v_infoState_1124_ = lean_ctor_get(v___x_1117_, 7);
v_snapshotTasks_1125_ = lean_ctor_get(v___x_1117_, 8);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v___x_1117_, 2);
lean_dec(v_unused_1135_);
v___x_1127_ = v___x_1117_;
v_isShared_1128_ = v_isSharedCheck_1134_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_snapshotTasks_1125_);
lean_inc(v_infoState_1124_);
lean_inc(v_messages_1123_);
lean_inc(v_cache_1122_);
lean_inc(v_traceState_1121_);
lean_inc(v_auxDeclNGen_1120_);
lean_inc(v_nextMacroScope_1119_);
lean_inc(v_env_1118_);
lean_dec(v___x_1117_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1134_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 2, v___x_1116_);
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_env_1118_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_nextMacroScope_1119_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_auxDeclNGen_1120_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_traceState_1121_);
lean_ctor_set(v_reuseFailAlloc_1133_, 5, v_cache_1122_);
lean_ctor_set(v_reuseFailAlloc_1133_, 6, v_messages_1123_);
lean_ctor_set(v_reuseFailAlloc_1133_, 7, v_infoState_1124_);
lean_ctor_set(v_reuseFailAlloc_1133_, 8, v_snapshotTasks_1125_);
v___x_1130_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_st_ref_put(v___y_1103_, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_r_1112_);
return v___x_1132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg___boxed(lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1138_);
lean_dec(v___y_1138_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(uint8_t v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v___x_1148_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1146_);
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3___boxed(lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v___y_18304__boxed_1164_; lean_object* v_res_1165_; 
v___y_18304__boxed_1164_ = lean_unbox(v___y_1157_);
v_res_1165_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_18304__boxed_1164_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1(lean_object* v_e_1166_, lean_object* v_args_1167_, lean_object* v_x_1168_, uint8_t v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1176_; uint8_t v___x_1177_; uint8_t v___x_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; 
v___x_1176_ = l_Lean_mkAppN(v_e_1166_, v_args_1167_);
v___x_1177_ = 0;
v___x_1178_ = 1;
v___x_1179_ = 1;
v___x_1180_ = l_Lean_Meta_mkLambdaFVars(v_args_1167_, v___x_1176_, v___x_1177_, v___x_1178_, v___x_1177_, v___x_1178_, v___x_1179_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__1___boxed(lean_object* v_e_1181_, lean_object* v_args_1182_, lean_object* v_x_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
uint8_t v___y_18345__boxed_1191_; lean_object* v_res_1192_; 
v___y_18345__boxed_1191_ = lean_unbox(v___y_1184_);
v_res_1192_ = l_Lean_Meta_Closure_collectExprAux___lam__1(v_e_1181_, v_args_1182_, v_x_1183_, v___y_18345__boxed_1191_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v_x_1183_);
lean_dec_ref(v_args_1182_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_x_1193_, lean_object* v_x_1194_){
_start:
{
if (lean_obj_tag(v_x_1194_) == 0)
{
return v_x_1193_;
}
else
{
lean_object* v_key_1195_; lean_object* v_value_1196_; lean_object* v_tail_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1220_; 
v_key_1195_ = lean_ctor_get(v_x_1194_, 0);
v_value_1196_ = lean_ctor_get(v_x_1194_, 1);
v_tail_1197_ = lean_ctor_get(v_x_1194_, 2);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_x_1194_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1199_ = v_x_1194_;
v_isShared_1200_ = v_isSharedCheck_1220_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_tail_1197_);
lean_inc(v_value_1196_);
lean_inc(v_key_1195_);
lean_dec(v_x_1194_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1220_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; uint64_t v___x_1202_; uint64_t v___x_1203_; uint64_t v___x_1204_; uint64_t v_fold_1205_; uint64_t v___x_1206_; uint64_t v___x_1207_; uint64_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1201_ = lean_array_get_size(v_x_1193_);
v___x_1202_ = l_Lean_ExprStructEq_hash(v_key_1195_);
v___x_1203_ = 32ULL;
v___x_1204_ = lean_uint64_shift_right(v___x_1202_, v___x_1203_);
v_fold_1205_ = lean_uint64_xor(v___x_1202_, v___x_1204_);
v___x_1206_ = 16ULL;
v___x_1207_ = lean_uint64_shift_right(v_fold_1205_, v___x_1206_);
v___x_1208_ = lean_uint64_xor(v_fold_1205_, v___x_1207_);
v___x_1209_ = lean_uint64_to_usize(v___x_1208_);
v___x_1210_ = lean_usize_of_nat(v___x_1201_);
v___x_1211_ = ((size_t)1ULL);
v___x_1212_ = lean_usize_sub(v___x_1210_, v___x_1211_);
v___x_1213_ = lean_usize_land(v___x_1209_, v___x_1212_);
v___x_1214_ = lean_array_uget_borrowed(v_x_1193_, v___x_1213_);
lean_inc(v___x_1214_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 2, v___x_1214_);
v___x_1216_ = v___x_1199_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_key_1195_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_value_1196_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_array_uset(v_x_1193_, v___x_1213_, v___x_1216_);
v_x_1193_ = v___x_1217_;
v_x_1194_ = v_tail_1197_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(lean_object* v_i_1221_, lean_object* v_source_1222_, lean_object* v_target_1223_){
_start:
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = lean_array_get_size(v_source_1222_);
v___x_1225_ = lean_nat_dec_lt(v_i_1221_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_dec_ref(v_source_1222_);
lean_dec(v_i_1221_);
return v_target_1223_;
}
else
{
lean_object* v_es_1226_; lean_object* v___x_1227_; lean_object* v_source_1228_; lean_object* v_target_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_es_1226_ = lean_array_fget(v_source_1222_, v_i_1221_);
v___x_1227_ = lean_box(0);
v_source_1228_ = lean_array_fset(v_source_1222_, v_i_1221_, v___x_1227_);
v_target_1229_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_target_1223_, v_es_1226_);
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_add(v_i_1221_, v___x_1230_);
lean_dec(v_i_1221_);
v_i_1221_ = v___x_1231_;
v_source_1222_ = v_source_1228_;
v_target_1223_ = v_target_1229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(lean_object* v_data_1233_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_nbuckets_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1234_ = lean_array_get_size(v_data_1233_);
v___x_1235_ = lean_unsigned_to_nat(2u);
v_nbuckets_1236_ = lean_nat_mul(v___x_1234_, v___x_1235_);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_box(0);
v___x_1239_ = lean_mk_array(v_nbuckets_1236_, v___x_1238_);
v___x_1240_ = lean_array_propagate_mark(v_data_1233_, v___x_1239_);
v___x_1241_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v___x_1237_, v_data_1233_, v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(lean_object* v_a_1242_, lean_object* v_b_1243_, lean_object* v_x_1244_){
_start:
{
if (lean_obj_tag(v_x_1244_) == 0)
{
lean_dec(v_b_1243_);
lean_dec_ref(v_a_1242_);
return v_x_1244_;
}
else
{
lean_object* v_key_1245_; lean_object* v_value_1246_; lean_object* v_tail_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1259_; 
v_key_1245_ = lean_ctor_get(v_x_1244_, 0);
v_value_1246_ = lean_ctor_get(v_x_1244_, 1);
v_tail_1247_ = lean_ctor_get(v_x_1244_, 2);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_x_1244_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1249_ = v_x_1244_;
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_tail_1247_);
lean_inc(v_value_1246_);
lean_inc(v_key_1245_);
lean_dec(v_x_1244_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
uint8_t v___x_1251_; 
v___x_1251_ = l_Lean_ExprStructEq_beq(v_key_1245_, v_a_1242_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1242_, v_b_1243_, v_tail_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 2, v___x_1252_);
v___x_1254_ = v___x_1249_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_key_1245_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_value_1246_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
else
{
lean_object* v___x_1257_; 
lean_dec(v_value_1246_);
lean_dec(v_key_1245_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v_b_1243_);
lean_ctor_set(v___x_1249_, 0, v_a_1242_);
v___x_1257_ = v___x_1249_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1242_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_b_1243_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_tail_1247_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(lean_object* v_a_1260_, lean_object* v_x_1261_){
_start:
{
if (lean_obj_tag(v_x_1261_) == 0)
{
uint8_t v___x_1262_; 
v___x_1262_ = 0;
return v___x_1262_;
}
else
{
lean_object* v_key_1263_; lean_object* v_tail_1264_; uint8_t v___x_1265_; 
v_key_1263_ = lean_ctor_get(v_x_1261_, 0);
v_tail_1264_ = lean_ctor_get(v_x_1261_, 2);
v___x_1265_ = l_Lean_ExprStructEq_beq(v_key_1263_, v_a_1260_);
if (v___x_1265_ == 0)
{
v_x_1261_ = v_tail_1264_;
goto _start;
}
else
{
return v___x_1265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg___boxed(lean_object* v_a_1267_, lean_object* v_x_1268_){
_start:
{
uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_res_1269_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1267_, v_x_1268_);
lean_dec(v_x_1268_);
lean_dec_ref(v_a_1267_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(lean_object* v_m_1271_, lean_object* v_a_1272_, lean_object* v_b_1273_){
_start:
{
lean_object* v_size_1274_; lean_object* v_buckets_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1318_; 
v_size_1274_ = lean_ctor_get(v_m_1271_, 0);
v_buckets_1275_ = lean_ctor_get(v_m_1271_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_m_1271_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1277_ = v_m_1271_;
v_isShared_1278_ = v_isSharedCheck_1318_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_buckets_1275_);
lean_inc(v_size_1274_);
lean_dec(v_m_1271_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1318_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; uint64_t v___x_1280_; uint64_t v___x_1281_; uint64_t v___x_1282_; uint64_t v_fold_1283_; uint64_t v___x_1284_; uint64_t v___x_1285_; uint64_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; lean_object* v_bkt_1292_; uint8_t v___x_1293_; 
v___x_1279_ = lean_array_get_size(v_buckets_1275_);
v___x_1280_ = l_Lean_ExprStructEq_hash(v_a_1272_);
v___x_1281_ = 32ULL;
v___x_1282_ = lean_uint64_shift_right(v___x_1280_, v___x_1281_);
v_fold_1283_ = lean_uint64_xor(v___x_1280_, v___x_1282_);
v___x_1284_ = 16ULL;
v___x_1285_ = lean_uint64_shift_right(v_fold_1283_, v___x_1284_);
v___x_1286_ = lean_uint64_xor(v_fold_1283_, v___x_1285_);
v___x_1287_ = lean_uint64_to_usize(v___x_1286_);
v___x_1288_ = lean_usize_of_nat(v___x_1279_);
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = lean_usize_sub(v___x_1288_, v___x_1289_);
v___x_1291_ = lean_usize_land(v___x_1287_, v___x_1290_);
v_bkt_1292_ = lean_array_uget_borrowed(v_buckets_1275_, v___x_1291_);
v___x_1293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1272_, v_bkt_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v_size_x27_1295_; lean_object* v___x_1296_; lean_object* v_buckets_x27_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1294_ = lean_unsigned_to_nat(1u);
v_size_x27_1295_ = lean_nat_add(v_size_1274_, v___x_1294_);
lean_dec(v_size_1274_);
lean_inc(v_bkt_1292_);
v___x_1296_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1296_, 0, v_a_1272_);
lean_ctor_set(v___x_1296_, 1, v_b_1273_);
lean_ctor_set(v___x_1296_, 2, v_bkt_1292_);
v_buckets_x27_1297_ = lean_array_uset(v_buckets_1275_, v___x_1291_, v___x_1296_);
v___x_1298_ = lean_unsigned_to_nat(4u);
v___x_1299_ = lean_nat_mul(v_size_x27_1295_, v___x_1298_);
v___x_1300_ = lean_unsigned_to_nat(3u);
v___x_1301_ = lean_nat_div(v___x_1299_, v___x_1300_);
lean_dec(v___x_1299_);
v___x_1302_ = lean_array_get_size(v_buckets_x27_1297_);
v___x_1303_ = lean_nat_dec_le(v___x_1301_, v___x_1302_);
lean_dec(v___x_1301_);
if (v___x_1303_ == 0)
{
lean_object* v_val_1304_; lean_object* v___x_1306_; 
v_val_1304_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_buckets_x27_1297_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v_val_1304_);
lean_ctor_set(v___x_1277_, 0, v_size_x27_1295_);
v___x_1306_ = v___x_1277_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_size_x27_1295_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_val_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
else
{
lean_object* v___x_1309_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v_buckets_x27_1297_);
lean_ctor_set(v___x_1277_, 0, v_size_x27_1295_);
v___x_1309_ = v___x_1277_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_size_x27_1295_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_buckets_x27_1297_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
else
{
lean_object* v___x_1311_; lean_object* v_buckets_x27_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_inc(v_bkt_1292_);
v___x_1311_ = lean_box(0);
v_buckets_x27_1312_ = lean_array_uset(v_buckets_1275_, v___x_1291_, v___x_1311_);
v___x_1313_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1272_, v_b_1273_, v_bkt_1292_);
v___x_1314_ = lean_array_uset(v_buckets_x27_1312_, v___x_1291_, v___x_1313_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___x_1314_);
v___x_1316_ = v___x_1277_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_size_1274_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux(lean_object* v_e_1319_, uint8_t v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
switch(lean_obj_tag(v_e_1319_))
{
case 11:
{
lean_object* v_typeName_1327_; lean_object* v_idx_1328_; lean_object* v_struct_1329_; lean_object* v___x_1330_; 
v_typeName_1327_ = lean_ctor_get(v_e_1319_, 0);
v_idx_1328_ = lean_ctor_get(v_e_1319_, 1);
v_struct_1329_ = lean_ctor_get(v_e_1319_, 2);
lean_inc_ref(v_struct_1329_);
v___x_1330_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_struct_1329_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1345_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1345_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1345_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
size_t v___x_1335_; size_t v___x_1336_; uint8_t v___x_1337_; 
v___x_1335_ = lean_ptr_addr(v_struct_1329_);
v___x_1336_ = lean_ptr_addr(v_a_1331_);
v___x_1337_ = lean_usize_dec_eq(v___x_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
lean_inc(v_idx_1328_);
lean_inc(v_typeName_1327_);
lean_dec_ref_known(v_e_1319_, 3);
v___x_1338_ = l_Lean_Expr_proj___override(v_typeName_1327_, v_idx_1328_, v_a_1331_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1338_);
v___x_1340_ = v___x_1333_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
else
{
lean_object* v___x_1343_; 
lean_dec(v_a_1331_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v_e_1319_);
v___x_1343_ = v___x_1333_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_e_1319_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1319_, 3);
return v___x_1330_;
}
}
case 7:
{
lean_object* v_binderName_1346_; lean_object* v_binderType_1347_; lean_object* v_body_1348_; uint8_t v_binderInfo_1349_; lean_object* v___x_1350_; 
v_binderName_1346_ = lean_ctor_get(v_e_1319_, 0);
v_binderType_1347_ = lean_ctor_get(v_e_1319_, 1);
v_body_1348_ = lean_ctor_get(v_e_1319_, 2);
v_binderInfo_1349_ = lean_ctor_get_uint8(v_e_1319_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1347_);
v___x_1350_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1347_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1352_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
lean_inc_ref(v_body_1348_);
v___x_1352_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1348_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1379_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1379_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1379_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
size_t v___x_1357_; size_t v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = lean_ptr_addr(v_binderType_1347_);
v___x_1358_ = lean_ptr_addr(v_a_1351_);
v___x_1359_ = lean_usize_dec_eq(v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
lean_inc(v_binderName_1346_);
lean_dec_ref_known(v_e_1319_, 3);
v___x_1360_ = l_Lean_Expr_forallE___override(v_binderName_1346_, v_a_1351_, v_a_1353_, v_binderInfo_1349_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1360_);
v___x_1362_ = v___x_1355_;
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
size_t v___x_1364_; size_t v___x_1365_; uint8_t v___x_1366_; 
v___x_1364_ = lean_ptr_addr(v_body_1348_);
v___x_1365_ = lean_ptr_addr(v_a_1353_);
v___x_1366_ = lean_usize_dec_eq(v___x_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
lean_inc(v_binderName_1346_);
lean_dec_ref_known(v_e_1319_, 3);
v___x_1367_ = l_Lean_Expr_forallE___override(v_binderName_1346_, v_a_1351_, v_a_1353_, v_binderInfo_1349_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1367_);
v___x_1369_ = v___x_1355_;
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
uint8_t v___x_1371_; 
v___x_1371_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1349_, v_binderInfo_1349_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_inc(v_binderName_1346_);
lean_dec_ref_known(v_e_1319_, 3);
v___x_1372_ = l_Lean_Expr_forallE___override(v_binderName_1346_, v_a_1351_, v_a_1353_, v_binderInfo_1349_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1372_);
v___x_1374_ = v___x_1355_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
else
{
lean_object* v___x_1377_; 
lean_dec(v_a_1353_);
lean_dec(v_a_1351_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v_e_1319_);
v___x_1377_ = v___x_1355_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_e_1319_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1351_);
lean_dec_ref_known(v_e_1319_, 3);
return v___x_1352_;
}
}
else
{
lean_dec_ref_known(v_e_1319_, 3);
return v___x_1350_;
}
}
case 6:
{
lean_object* v_binderName_1380_; lean_object* v_binderType_1381_; lean_object* v_body_1382_; uint8_t v_binderInfo_1383_; lean_object* v___x_1384_; 
v_binderName_1380_ = lean_ctor_get(v_e_1319_, 0);
v_binderType_1381_ = lean_ctor_get(v_e_1319_, 1);
v_body_1382_ = lean_ctor_get(v_e_1319_, 2);
v_binderInfo_1383_ = lean_ctor_get_uint8(v_e_1319_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1381_);
v___x_1384_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_binderType_1381_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
lean_inc_ref(v_body_1382_);
v___x_1386_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1382_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1413_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1413_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1413_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
size_t v___x_1391_; size_t v___x_1392_; uint8_t v___x_1393_; 
v___x_1391_ = lean_ptr_addr(v_binderType_1381_);
v___x_1392_ = lean_ptr_addr(v_a_1385_);
v___x_1393_ = lean_usize_dec_eq(v___x_1391_, v___x_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
lean_inc(v_binderName_1380_);
lean_dec_ref_known(v_e_1319_, 3);
v___x_1394_ = l_Lean_Expr_lam___override(v_binderName_1380_, v_a_1385_, v_a_1387_, v_binderInfo_1383_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1394_);
v___x_1396_ = v___x_1389_;
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
size_t v___x_1398_; size_t v___x_1399_; uint8_t v___x_1400_; 
v___x_1398_ = lean_ptr_addr(v_body_1382_);
v___x_1399_ = lean_ptr_addr(v_a_1387_);
v___x_1400_ = lean_usize_dec_eq(v___x_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
lean_inc(v_binderName_1380_);
lean_dec_ref_known(v_e_1319_, 3);
v___x_1401_ = l_Lean_Expr_lam___override(v_binderName_1380_, v_a_1385_, v_a_1387_, v_binderInfo_1383_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1401_);
v___x_1403_ = v___x_1389_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
else
{
uint8_t v___x_1405_; 
v___x_1405_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1383_, v_binderInfo_1383_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
lean_inc(v_binderName_1380_);
lean_dec_ref_known(v_e_1319_, 3);
v___x_1406_ = l_Lean_Expr_lam___override(v_binderName_1380_, v_a_1385_, v_a_1387_, v_binderInfo_1383_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1406_);
v___x_1408_ = v___x_1389_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
else
{
lean_object* v___x_1411_; 
lean_dec(v_a_1387_);
lean_dec(v_a_1385_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v_e_1319_);
v___x_1411_ = v___x_1389_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_e_1319_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1385_);
lean_dec_ref_known(v_e_1319_, 3);
return v___x_1386_;
}
}
else
{
lean_dec_ref_known(v_e_1319_, 3);
return v___x_1384_;
}
}
case 8:
{
lean_object* v_declName_1414_; lean_object* v_type_1415_; lean_object* v_value_1416_; lean_object* v_body_1417_; uint8_t v_nondep_1418_; lean_object* v___x_1419_; 
v_declName_1414_ = lean_ctor_get(v_e_1319_, 0);
v_type_1415_ = lean_ctor_get(v_e_1319_, 1);
v_value_1416_ = lean_ctor_get(v_e_1319_, 2);
v_body_1417_ = lean_ctor_get(v_e_1319_, 3);
v_nondep_1418_ = lean_ctor_get_uint8(v_e_1319_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1415_);
v___x_1419_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_type_1415_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1421_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
lean_inc_ref(v_value_1416_);
v___x_1421_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_value_1416_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
lean_inc_ref(v_body_1417_);
v___x_1423_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_body_1417_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1452_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1452_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1452_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
size_t v___x_1428_; size_t v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = lean_ptr_addr(v_type_1415_);
v___x_1429_ = lean_ptr_addr(v_a_1420_);
v___x_1430_ = lean_usize_dec_eq(v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
lean_inc(v_declName_1414_);
lean_dec_ref_known(v_e_1319_, 4);
v___x_1431_ = l_Lean_Expr_letE___override(v_declName_1414_, v_a_1420_, v_a_1422_, v_a_1424_, v_nondep_1418_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1431_);
v___x_1433_ = v___x_1426_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
else
{
size_t v___x_1435_; size_t v___x_1436_; uint8_t v___x_1437_; 
v___x_1435_ = lean_ptr_addr(v_value_1416_);
v___x_1436_ = lean_ptr_addr(v_a_1422_);
v___x_1437_ = lean_usize_dec_eq(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_inc(v_declName_1414_);
lean_dec_ref_known(v_e_1319_, 4);
v___x_1438_ = l_Lean_Expr_letE___override(v_declName_1414_, v_a_1420_, v_a_1422_, v_a_1424_, v_nondep_1418_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1438_);
v___x_1440_ = v___x_1426_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
else
{
size_t v___x_1442_; size_t v___x_1443_; uint8_t v___x_1444_; 
v___x_1442_ = lean_ptr_addr(v_body_1417_);
v___x_1443_ = lean_ptr_addr(v_a_1424_);
v___x_1444_ = lean_usize_dec_eq(v___x_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
lean_inc(v_declName_1414_);
lean_dec_ref_known(v_e_1319_, 4);
v___x_1445_ = l_Lean_Expr_letE___override(v_declName_1414_, v_a_1420_, v_a_1422_, v_a_1424_, v_nondep_1418_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1445_);
v___x_1447_ = v___x_1426_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
else
{
lean_object* v___x_1450_; 
lean_dec(v_a_1424_);
lean_dec(v_a_1422_);
lean_dec(v_a_1420_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v_e_1319_);
v___x_1450_ = v___x_1426_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_e_1319_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1422_);
lean_dec(v_a_1420_);
lean_dec_ref_known(v_e_1319_, 4);
return v___x_1423_;
}
}
else
{
lean_dec(v_a_1420_);
lean_dec_ref_known(v_e_1319_, 4);
return v___x_1421_;
}
}
else
{
lean_dec_ref_known(v_e_1319_, 4);
return v___x_1419_;
}
}
case 5:
{
lean_object* v_fn_1453_; lean_object* v_arg_1454_; lean_object* v___x_1455_; 
v_fn_1453_ = lean_ctor_get(v_e_1319_, 0);
v_arg_1454_ = lean_ctor_get(v_e_1319_, 1);
lean_inc_ref(v_fn_1453_);
v___x_1455_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_fn_1453_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
lean_inc_ref(v_arg_1454_);
v___x_1457_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_arg_1454_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1479_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1479_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1479_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
size_t v___x_1462_; size_t v___x_1463_; uint8_t v___x_1464_; 
v___x_1462_ = lean_ptr_addr(v_fn_1453_);
v___x_1463_ = lean_ptr_addr(v_a_1456_);
v___x_1464_ = lean_usize_dec_eq(v___x_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_dec_ref_known(v_e_1319_, 2);
v___x_1465_ = l_Lean_Expr_app___override(v_a_1456_, v_a_1458_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1465_);
v___x_1467_ = v___x_1460_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
else
{
size_t v___x_1469_; size_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = lean_ptr_addr(v_arg_1454_);
v___x_1470_ = lean_ptr_addr(v_a_1458_);
v___x_1471_ = lean_usize_dec_eq(v___x_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_dec_ref_known(v_e_1319_, 2);
v___x_1472_ = l_Lean_Expr_app___override(v_a_1456_, v_a_1458_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1472_);
v___x_1474_ = v___x_1460_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
else
{
lean_object* v___x_1477_; 
lean_dec(v_a_1458_);
lean_dec(v_a_1456_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v_e_1319_);
v___x_1477_ = v___x_1460_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_e_1319_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
else
{
lean_dec(v_a_1456_);
lean_dec_ref_known(v_e_1319_, 2);
return v___x_1457_;
}
}
else
{
lean_dec_ref_known(v_e_1319_, 2);
return v___x_1455_;
}
}
case 10:
{
lean_object* v_data_1480_; lean_object* v_expr_1481_; lean_object* v___x_1482_; 
v_data_1480_ = lean_ctor_get(v_e_1319_, 0);
v_expr_1481_ = lean_ctor_get(v_e_1319_, 1);
lean_inc_ref(v_expr_1481_);
v___x_1482_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_expr_1481_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1497_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1497_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1497_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
size_t v___x_1487_; size_t v___x_1488_; uint8_t v___x_1489_; 
v___x_1487_ = lean_ptr_addr(v_expr_1481_);
v___x_1488_ = lean_ptr_addr(v_a_1483_);
v___x_1489_ = lean_usize_dec_eq(v___x_1487_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_inc(v_data_1480_);
lean_dec_ref_known(v_e_1319_, 2);
v___x_1490_ = l_Lean_Expr_mdata___override(v_data_1480_, v_a_1483_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1490_);
v___x_1492_ = v___x_1485_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
else
{
lean_object* v___x_1495_; 
lean_dec(v_a_1483_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v_e_1319_);
v___x_1495_ = v___x_1485_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_e_1319_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_1319_, 2);
return v___x_1482_;
}
}
case 3:
{
lean_object* v_u_1498_; lean_object* v___x_1499_; 
v_u_1498_ = lean_ctor_get(v_e_1319_, 0);
lean_inc(v_u_1498_);
v___x_1499_ = l_Lean_Meta_Closure_collectLevel___redArg(v_u_1498_, v_a_1321_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1514_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1514_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1514_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
size_t v___x_1504_; size_t v___x_1505_; uint8_t v___x_1506_; 
v___x_1504_ = lean_ptr_addr(v_u_1498_);
v___x_1505_ = lean_ptr_addr(v_a_1500_);
v___x_1506_ = lean_usize_dec_eq(v___x_1504_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
lean_dec_ref_known(v_e_1319_, 1);
v___x_1507_ = l_Lean_Expr_sort___override(v_a_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1507_);
v___x_1509_ = v___x_1502_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
else
{
lean_object* v___x_1512_; 
lean_dec(v_a_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v_e_1319_);
v___x_1512_ = v___x_1502_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_e_1319_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec_ref_known(v_e_1319_, 1);
v_a_1515_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1499_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1499_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
case 4:
{
lean_object* v_declName_1523_; lean_object* v_us_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_declName_1523_ = lean_ctor_get(v_e_1319_, 0);
v_us_1524_ = lean_ctor_get(v_e_1319_, 1);
v___x_1525_ = lean_box(0);
lean_inc(v_us_1524_);
v___x_1526_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_us_1524_, v___x_1525_, v_a_1321_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1539_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1529_ = v___x_1526_;
v_isShared_1530_ = v_isSharedCheck_1539_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1526_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1539_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
uint8_t v___x_1531_; 
v___x_1531_ = l_ptrEqList___redArg(v_us_1524_, v_a_1527_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
lean_inc(v_declName_1523_);
lean_dec_ref_known(v_e_1319_, 2);
v___x_1532_ = l_Lean_Expr_const___override(v_declName_1523_, v_a_1527_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1532_);
v___x_1534_ = v___x_1529_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
else
{
lean_object* v___x_1537_; 
lean_dec(v_a_1527_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v_e_1319_);
v___x_1537_ = v___x_1529_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_e_1319_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec_ref_known(v_e_1319_, 2);
v_a_1540_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1526_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1526_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; 
v_mvarId_1548_ = lean_ctor_get(v_e_1319_, 0);
lean_inc_ref(v_e_1319_);
v___f_1549_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_collectExprAux___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1549_, 0, v_e_1319_);
lean_inc(v_mvarId_1548_);
v___x_1550_ = l_Lean_MVarId_getDecl(v_mvarId_1548_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v_type_1552_; lean_object* v___x_1553_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v_type_1552_ = lean_ctor_get(v_a_1551_, 2);
lean_inc_ref_n(v_type_1552_, 2);
lean_dec(v_a_1551_);
v___x_1553_ = l_Lean_Meta_Closure_preprocess(v_type_1552_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1555_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1554_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1557_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1559_ = l_Lean_Meta_Closure_mkNextUserName___redArg(v_a_1321_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1621_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1621_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1621_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v_e_x27_1565_; lean_object* v___y_1566_; lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_getDelayedMVarAssignment_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__4___redArg(v_mvarId_1548_, v_a_1323_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
if (lean_obj_tag(v_a_1599_) == 1)
{
lean_object* v_val_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1612_; 
lean_dec_ref_known(v_e_1319_, 1);
v_val_1600_ = lean_ctor_get(v_a_1599_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_a_1599_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1602_ = v_a_1599_;
v_isShared_1603_ = v_isSharedCheck_1612_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_val_1600_);
lean_dec(v_a_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1612_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v_fvars_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
v_fvars_1604_ = lean_ctor_get(v_val_1600_, 0);
lean_inc_ref(v_fvars_1604_);
lean_dec(v_val_1600_);
v___x_1605_ = lean_array_get_size(v_fvars_1604_);
lean_dec_ref(v_fvars_1604_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1605_);
v___x_1607_ = v___x_1602_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
uint8_t v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = 0;
v___x_1609_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Closure_collectExprAux_spec__5___redArg(v_type_1552_, v___x_1607_, v___f_1549_, v___x_1608_, v___x_1608_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v_e_x27_1565_ = v_a_1610_;
v___y_1566_ = v_a_1321_;
goto v___jp_1564_;
}
else
{
lean_del_object(v___x_1562_);
lean_dec(v_a_1560_);
lean_dec(v_a_1558_);
lean_dec(v_a_1556_);
return v___x_1609_;
}
}
}
}
else
{
lean_dec(v_a_1599_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v___f_1549_);
v_e_x27_1565_ = v_e_1319_;
v___y_1566_ = v_a_1321_;
goto v___jp_1564_;
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_del_object(v___x_1562_);
lean_dec(v_a_1560_);
lean_dec(v_a_1558_);
lean_dec(v_a_1556_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v___f_1549_);
lean_dec_ref_known(v_e_1319_, 1);
v_a_1613_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1598_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1598_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
v___jp_1564_:
{
lean_object* v___x_1567_; lean_object* v_visitedLevel_1568_; lean_object* v_visitedExpr_1569_; lean_object* v_levelParams_1570_; lean_object* v_nextLevelIdx_1571_; lean_object* v_levelArgs_1572_; lean_object* v_newLocalDecls_1573_; lean_object* v_newLocalDeclsForMVars_1574_; lean_object* v_newLetDecls_1575_; lean_object* v_nextExprIdx_1576_; lean_object* v_exprMVarArgs_1577_; lean_object* v_exprFVarArgs_1578_; lean_object* v_toProcess_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1597_; 
v___x_1567_ = lean_st_ref_take(v___y_1566_);
v_visitedLevel_1568_ = lean_ctor_get(v___x_1567_, 0);
v_visitedExpr_1569_ = lean_ctor_get(v___x_1567_, 1);
v_levelParams_1570_ = lean_ctor_get(v___x_1567_, 2);
v_nextLevelIdx_1571_ = lean_ctor_get(v___x_1567_, 3);
v_levelArgs_1572_ = lean_ctor_get(v___x_1567_, 4);
v_newLocalDecls_1573_ = lean_ctor_get(v___x_1567_, 5);
v_newLocalDeclsForMVars_1574_ = lean_ctor_get(v___x_1567_, 6);
v_newLetDecls_1575_ = lean_ctor_get(v___x_1567_, 7);
v_nextExprIdx_1576_ = lean_ctor_get(v___x_1567_, 8);
v_exprMVarArgs_1577_ = lean_ctor_get(v___x_1567_, 9);
v_exprFVarArgs_1578_ = lean_ctor_get(v___x_1567_, 10);
v_toProcess_1579_ = lean_ctor_get(v___x_1567_, 11);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1581_ = v___x_1567_;
v_isShared_1582_ = v_isSharedCheck_1597_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_toProcess_1579_);
lean_inc(v_exprFVarArgs_1578_);
lean_inc(v_exprMVarArgs_1577_);
lean_inc(v_nextExprIdx_1576_);
lean_inc(v_newLetDecls_1575_);
lean_inc(v_newLocalDeclsForMVars_1574_);
lean_inc(v_newLocalDecls_1573_);
lean_inc(v_levelArgs_1572_);
lean_inc(v_nextLevelIdx_1571_);
lean_inc(v_levelParams_1570_);
lean_inc(v_visitedExpr_1569_);
lean_inc(v_visitedLevel_1568_);
lean_dec(v___x_1567_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1597_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; uint8_t v___x_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1583_ = lean_unsigned_to_nat(0u);
v___x_1584_ = 0;
v___x_1585_ = 0;
lean_inc(v_a_1558_);
v___x_1586_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1586_, 0, v___x_1583_);
lean_ctor_set(v___x_1586_, 1, v_a_1558_);
lean_ctor_set(v___x_1586_, 2, v_a_1560_);
lean_ctor_set(v___x_1586_, 3, v_a_1556_);
lean_ctor_set_uint8(v___x_1586_, sizeof(void*)*4, v___x_1584_);
lean_ctor_set_uint8(v___x_1586_, sizeof(void*)*4 + 1, v___x_1585_);
v___x_1587_ = lean_array_push(v_newLocalDeclsForMVars_1574_, v___x_1586_);
v___x_1588_ = lean_array_push(v_exprMVarArgs_1577_, v_e_x27_1565_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 9, v___x_1588_);
lean_ctor_set(v___x_1581_, 6, v___x_1587_);
v___x_1590_ = v___x_1581_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_visitedLevel_1568_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_visitedExpr_1569_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_levelParams_1570_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_nextLevelIdx_1571_);
lean_ctor_set(v_reuseFailAlloc_1596_, 4, v_levelArgs_1572_);
lean_ctor_set(v_reuseFailAlloc_1596_, 5, v_newLocalDecls_1573_);
lean_ctor_set(v_reuseFailAlloc_1596_, 6, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1596_, 7, v_newLetDecls_1575_);
lean_ctor_set(v_reuseFailAlloc_1596_, 8, v_nextExprIdx_1576_);
lean_ctor_set(v_reuseFailAlloc_1596_, 9, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1596_, 10, v_exprFVarArgs_1578_);
lean_ctor_set(v_reuseFailAlloc_1596_, 11, v_toProcess_1579_);
v___x_1590_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1591_ = lean_st_ref_put(v___y_1566_, v___x_1590_);
v___x_1592_ = l_Lean_mkFVar(v_a_1558_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1592_);
v___x_1594_ = v___x_1562_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_a_1558_);
lean_dec(v_a_1556_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v___f_1549_);
lean_dec_ref_known(v_e_1319_, 1);
v_a_1622_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1559_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1559_);
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
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v_a_1556_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v___f_1549_);
lean_dec_ref_known(v_e_1319_, 1);
v_a_1630_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1557_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1557_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_dec_ref(v_type_1552_);
lean_dec_ref(v___f_1549_);
lean_dec_ref_known(v_e_1319_, 1);
return v___x_1555_;
}
}
else
{
lean_dec_ref(v_type_1552_);
lean_dec_ref(v___f_1549_);
lean_dec_ref_known(v_e_1319_, 1);
return v___x_1553_;
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v___f_1549_);
lean_dec_ref_known(v_e_1319_, 1);
v_a_1638_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1550_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1550_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_1646_; uint8_t v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; uint8_t v___x_1683_; lean_object* v___x_1684_; 
v_fvarId_1646_ = lean_ctor_get(v_e_1319_, 0);
lean_inc_n(v_fvarId_1646_, 2);
lean_dec_ref_known(v_e_1319_, 1);
v___x_1683_ = 0;
v___x_1684_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_1646_, v___x_1683_, v_a_1322_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1684_) == 0)
{
if (v_a_1320_ == 1)
{
lean_object* v_a_1685_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1684_, 1);
if (lean_obj_tag(v_a_1685_) == 1)
{
lean_object* v_val_1686_; lean_object* v___x_1687_; 
lean_dec(v_fvarId_1646_);
v_val_1686_ = lean_ctor_get(v_a_1685_, 0);
lean_inc(v_val_1686_);
lean_dec_ref_known(v_a_1685_, 1);
v___x_1687_ = l_Lean_Meta_Closure_preprocess(v_val_1686_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1689_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_a_1688_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1689_;
}
else
{
return v___x_1687_;
}
}
else
{
lean_dec(v_a_1685_);
v___y_1648_ = v_a_1320_;
v___y_1649_ = v_a_1321_;
v___y_1650_ = v_a_1322_;
v___y_1651_ = v_a_1323_;
v___y_1652_ = v_a_1324_;
v___y_1653_ = v_a_1325_;
goto v___jp_1647_;
}
}
else
{
lean_dec_ref_known(v___x_1684_, 1);
v___y_1648_ = v_a_1320_;
v___y_1649_ = v_a_1321_;
v___y_1650_ = v_a_1322_;
v___y_1651_ = v_a_1323_;
v___y_1652_ = v_a_1324_;
v___y_1653_ = v_a_1325_;
goto v___jp_1647_;
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v_fvarId_1646_);
v_a_1690_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1684_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1684_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
v___jp_1647_:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3(v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc_n(v_a_1655_, 2);
lean_dec_ref_known(v___x_1654_, 1);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v_fvarId_1646_);
lean_ctor_set(v___x_1656_, 1, v_a_1655_);
v___x_1657_ = l_Lean_Meta_Closure_pushToProcess___redArg(v___x_1656_, v___y_1649_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1665_; 
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v___x_1657_, 0);
lean_dec(v_unused_1666_);
v___x_1659_ = v___x_1657_;
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
else
{
lean_dec(v___x_1657_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = l_Lean_mkFVar(v_a_1655_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1661_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v_a_1655_);
v_a_1667_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1657_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1657_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec(v_fvarId_1646_);
v_a_1675_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1654_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1654_);
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
}
}
default: 
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1698_, 0, v_e_1319_);
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0(lean_object* v_e_1699_, uint8_t v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v___x_1750_; 
v___x_1750_ = l_Lean_Expr_hasLevelParam(v_e_1699_);
if (v___x_1750_ == 0)
{
uint8_t v___x_1751_; 
v___x_1751_ = l_Lean_Expr_hasFVar(v_e_1699_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; 
v___x_1752_ = l_Lean_Expr_hasMVar(v_e_1699_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_e_1699_);
return v___x_1753_;
}
else
{
goto v___jp_1707_;
}
}
else
{
goto v___jp_1707_;
}
}
else
{
goto v___jp_1707_;
}
v___jp_1707_:
{
lean_object* v___x_1708_; lean_object* v_visitedExpr_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_st_ref_get(v___y_1701_);
v_visitedExpr_1709_ = lean_ctor_get(v___x_1708_, 1);
lean_inc_ref(v_visitedExpr_1709_);
lean_dec(v___x_1708_);
v___x_1710_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1709_, v_e_1699_);
lean_dec_ref(v_visitedExpr_1709_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v___x_1711_; 
lean_inc_ref(v_e_1699_);
v___x_1711_ = l_Lean_Meta_Closure_collectExprAux(v_e_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1741_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1741_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1741_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v_visitedLevel_1717_; lean_object* v_visitedExpr_1718_; lean_object* v_levelParams_1719_; lean_object* v_nextLevelIdx_1720_; lean_object* v_levelArgs_1721_; lean_object* v_newLocalDecls_1722_; lean_object* v_newLocalDeclsForMVars_1723_; lean_object* v_newLetDecls_1724_; lean_object* v_nextExprIdx_1725_; lean_object* v_exprMVarArgs_1726_; lean_object* v_exprFVarArgs_1727_; lean_object* v_toProcess_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1740_; 
v___x_1716_ = lean_st_ref_take(v___y_1701_);
v_visitedLevel_1717_ = lean_ctor_get(v___x_1716_, 0);
v_visitedExpr_1718_ = lean_ctor_get(v___x_1716_, 1);
v_levelParams_1719_ = lean_ctor_get(v___x_1716_, 2);
v_nextLevelIdx_1720_ = lean_ctor_get(v___x_1716_, 3);
v_levelArgs_1721_ = lean_ctor_get(v___x_1716_, 4);
v_newLocalDecls_1722_ = lean_ctor_get(v___x_1716_, 5);
v_newLocalDeclsForMVars_1723_ = lean_ctor_get(v___x_1716_, 6);
v_newLetDecls_1724_ = lean_ctor_get(v___x_1716_, 7);
v_nextExprIdx_1725_ = lean_ctor_get(v___x_1716_, 8);
v_exprMVarArgs_1726_ = lean_ctor_get(v___x_1716_, 9);
v_exprFVarArgs_1727_ = lean_ctor_get(v___x_1716_, 10);
v_toProcess_1728_ = lean_ctor_get(v___x_1716_, 11);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1730_ = v___x_1716_;
v_isShared_1731_ = v_isSharedCheck_1740_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_toProcess_1728_);
lean_inc(v_exprFVarArgs_1727_);
lean_inc(v_exprMVarArgs_1726_);
lean_inc(v_nextExprIdx_1725_);
lean_inc(v_newLetDecls_1724_);
lean_inc(v_newLocalDeclsForMVars_1723_);
lean_inc(v_newLocalDecls_1722_);
lean_inc(v_levelArgs_1721_);
lean_inc(v_nextLevelIdx_1720_);
lean_inc(v_levelParams_1719_);
lean_inc(v_visitedExpr_1718_);
lean_inc(v_visitedLevel_1717_);
lean_dec(v___x_1716_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1740_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_inc(v_a_1712_);
v___x_1732_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1718_, v_e_1699_, v_a_1712_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 1, v___x_1732_);
v___x_1734_ = v___x_1730_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_visitedLevel_1717_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1739_, 2, v_levelParams_1719_);
lean_ctor_set(v_reuseFailAlloc_1739_, 3, v_nextLevelIdx_1720_);
lean_ctor_set(v_reuseFailAlloc_1739_, 4, v_levelArgs_1721_);
lean_ctor_set(v_reuseFailAlloc_1739_, 5, v_newLocalDecls_1722_);
lean_ctor_set(v_reuseFailAlloc_1739_, 6, v_newLocalDeclsForMVars_1723_);
lean_ctor_set(v_reuseFailAlloc_1739_, 7, v_newLetDecls_1724_);
lean_ctor_set(v_reuseFailAlloc_1739_, 8, v_nextExprIdx_1725_);
lean_ctor_set(v_reuseFailAlloc_1739_, 9, v_exprMVarArgs_1726_);
lean_ctor_set(v_reuseFailAlloc_1739_, 10, v_exprFVarArgs_1727_);
lean_ctor_set(v_reuseFailAlloc_1739_, 11, v_toProcess_1728_);
v___x_1734_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1735_ = lean_st_ref_put(v___y_1701_, v___x_1734_);
if (v_isShared_1715_ == 0)
{
v___x_1737_ = v___x_1714_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1712_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1699_);
return v___x_1711_;
}
}
else
{
lean_object* v_val_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_e_1699_);
v_val_1742_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1710_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_val_1742_);
lean_dec(v___x_1710_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set_tag(v___x_1744_, 0);
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_val_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___lam__0___boxed(lean_object* v_e_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
uint8_t v___y_18584__boxed_1762_; lean_object* v_res_1763_; 
v___y_18584__boxed_1762_ = lean_unbox(v___y_1755_);
v_res_1763_ = l_Lean_Meta_Closure_collectExprAux___lam__0(v_e_1754_, v___y_18584__boxed_1762_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExprAux___boxed(lean_object* v_e_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
uint8_t v_a_boxed_1772_; lean_object* v_res_1773_; 
v_a_boxed_1772_ = lean_unbox(v_a_1765_);
v_res_1773_ = l_Lean_Meta_Closure_collectExprAux(v_e_1764_, v_a_boxed_1772_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(lean_object* v_00_u03b2_1774_, lean_object* v_m_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_m_1775_, v_a_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___boxed(lean_object* v_00_u03b2_1778_, lean_object* v_m_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0(v_00_u03b2_1778_, v_m_1779_, v_a_1780_);
lean_dec_ref(v_a_1780_);
lean_dec_ref(v_m_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1(lean_object* v_00_u03b2_1782_, lean_object* v_m_1783_, lean_object* v_a_1784_, lean_object* v_b_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_m_1783_, v_a_1784_, v_b_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(lean_object* v_x_1787_, lean_object* v_x_1788_, uint8_t v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___redArg(v_x_1787_, v_x_1788_, v___y_1790_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2___boxed(lean_object* v_x_1797_, lean_object* v_x_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
uint8_t v___y_19416__boxed_1806_; lean_object* v_res_1807_; 
v___y_19416__boxed_1806_ = lean_unbox(v___y_1799_);
v_res_1807_ = l_List_mapM_loop___at___00Lean_Meta_Closure_collectExprAux_spec__2(v_x_1797_, v_x_1798_, v___y_19416__boxed_1806_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(uint8_t v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___redArg(v___y_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7___boxed(lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
uint8_t v___y_19443__boxed_1823_; lean_object* v_res_1824_; 
v___y_19443__boxed_1823_ = lean_unbox(v___y_1816_);
v_res_1824_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Closure_collectExprAux_spec__3_spec__7(v___y_19443__boxed_1823_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(lean_object* v_00_u03b2_1825_, lean_object* v_a_1826_, lean_object* v_x_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___redArg(v_a_1826_, v_x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1829_, lean_object* v_a_1830_, lean_object* v_x_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0_spec__0(v_00_u03b2_1829_, v_a_1830_, v_x_1831_);
lean_dec(v_x_1831_);
lean_dec_ref(v_a_1830_);
return v_res_1832_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(lean_object* v_00_u03b2_1833_, lean_object* v_a_1834_, lean_object* v_x_1835_){
_start:
{
uint8_t v___x_1836_; 
v___x_1836_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___redArg(v_a_1834_, v_x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1837_, lean_object* v_a_1838_, lean_object* v_x_1839_){
_start:
{
uint8_t v_res_1840_; lean_object* v_r_1841_; 
v_res_1840_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__2(v_00_u03b2_1837_, v_a_1838_, v_x_1839_);
lean_dec(v_x_1839_);
lean_dec_ref(v_a_1838_);
v_r_1841_ = lean_box(v_res_1840_);
return v_r_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3(lean_object* v_00_u03b2_1842_, lean_object* v_data_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3___redArg(v_data_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4(lean_object* v_00_u03b2_1845_, lean_object* v_a_1846_, lean_object* v_b_1847_, lean_object* v_x_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__4___redArg(v_a_1846_, v_b_1847_, v_x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1850_, lean_object* v_i_1851_, lean_object* v_source_1852_, lean_object* v_target_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6___redArg(v_i_1851_, v_source_1852_, v_target_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1_spec__3_spec__6_spec__10___redArg(v_x_1856_, v_x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr(lean_object* v_e_1859_, uint8_t v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Meta_Closure_preprocess(v_e_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; uint8_t v___x_1912_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
v___x_1912_ = l_Lean_Expr_hasLevelParam(v_a_1868_);
if (v___x_1912_ == 0)
{
uint8_t v___x_1913_; 
v___x_1913_ = l_Lean_Expr_hasFVar(v_a_1868_);
if (v___x_1913_ == 0)
{
uint8_t v___x_1914_; 
v___x_1914_ = l_Lean_Expr_hasMVar(v_a_1868_);
if (v___x_1914_ == 0)
{
lean_dec(v_a_1868_);
return v___x_1867_;
}
else
{
lean_dec_ref_known(v___x_1867_, 1);
goto v___jp_1869_;
}
}
else
{
lean_dec_ref_known(v___x_1867_, 1);
goto v___jp_1869_;
}
}
else
{
lean_dec_ref_known(v___x_1867_, 1);
goto v___jp_1869_;
}
v___jp_1869_:
{
lean_object* v___x_1870_; lean_object* v_visitedExpr_1871_; lean_object* v___x_1872_; 
v___x_1870_ = lean_st_ref_get(v_a_1861_);
v_visitedExpr_1871_ = lean_ctor_get(v___x_1870_, 1);
lean_inc_ref(v_visitedExpr_1871_);
lean_dec(v___x_1870_);
v___x_1872_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Closure_collectExprAux_spec__0___redArg(v_visitedExpr_1871_, v_a_1868_);
lean_dec_ref(v_visitedExpr_1871_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v___x_1873_; 
lean_inc(v_a_1868_);
v___x_1873_ = l_Lean_Meta_Closure_collectExprAux(v_a_1868_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1903_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1903_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1903_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v_visitedLevel_1879_; lean_object* v_visitedExpr_1880_; lean_object* v_levelParams_1881_; lean_object* v_nextLevelIdx_1882_; lean_object* v_levelArgs_1883_; lean_object* v_newLocalDecls_1884_; lean_object* v_newLocalDeclsForMVars_1885_; lean_object* v_newLetDecls_1886_; lean_object* v_nextExprIdx_1887_; lean_object* v_exprMVarArgs_1888_; lean_object* v_exprFVarArgs_1889_; lean_object* v_toProcess_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1902_; 
v___x_1878_ = lean_st_ref_take(v_a_1861_);
v_visitedLevel_1879_ = lean_ctor_get(v___x_1878_, 0);
v_visitedExpr_1880_ = lean_ctor_get(v___x_1878_, 1);
v_levelParams_1881_ = lean_ctor_get(v___x_1878_, 2);
v_nextLevelIdx_1882_ = lean_ctor_get(v___x_1878_, 3);
v_levelArgs_1883_ = lean_ctor_get(v___x_1878_, 4);
v_newLocalDecls_1884_ = lean_ctor_get(v___x_1878_, 5);
v_newLocalDeclsForMVars_1885_ = lean_ctor_get(v___x_1878_, 6);
v_newLetDecls_1886_ = lean_ctor_get(v___x_1878_, 7);
v_nextExprIdx_1887_ = lean_ctor_get(v___x_1878_, 8);
v_exprMVarArgs_1888_ = lean_ctor_get(v___x_1878_, 9);
v_exprFVarArgs_1889_ = lean_ctor_get(v___x_1878_, 10);
v_toProcess_1890_ = lean_ctor_get(v___x_1878_, 11);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1892_ = v___x_1878_;
v_isShared_1893_ = v_isSharedCheck_1902_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_toProcess_1890_);
lean_inc(v_exprFVarArgs_1889_);
lean_inc(v_exprMVarArgs_1888_);
lean_inc(v_nextExprIdx_1887_);
lean_inc(v_newLetDecls_1886_);
lean_inc(v_newLocalDeclsForMVars_1885_);
lean_inc(v_newLocalDecls_1884_);
lean_inc(v_levelArgs_1883_);
lean_inc(v_nextLevelIdx_1882_);
lean_inc(v_levelParams_1881_);
lean_inc(v_visitedExpr_1880_);
lean_inc(v_visitedLevel_1879_);
lean_dec(v___x_1878_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1902_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
lean_inc(v_a_1874_);
v___x_1894_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Closure_collectExprAux_spec__1___redArg(v_visitedExpr_1880_, v_a_1868_, v_a_1874_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v___x_1894_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_visitedLevel_1879_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_levelParams_1881_);
lean_ctor_set(v_reuseFailAlloc_1901_, 3, v_nextLevelIdx_1882_);
lean_ctor_set(v_reuseFailAlloc_1901_, 4, v_levelArgs_1883_);
lean_ctor_set(v_reuseFailAlloc_1901_, 5, v_newLocalDecls_1884_);
lean_ctor_set(v_reuseFailAlloc_1901_, 6, v_newLocalDeclsForMVars_1885_);
lean_ctor_set(v_reuseFailAlloc_1901_, 7, v_newLetDecls_1886_);
lean_ctor_set(v_reuseFailAlloc_1901_, 8, v_nextExprIdx_1887_);
lean_ctor_set(v_reuseFailAlloc_1901_, 9, v_exprMVarArgs_1888_);
lean_ctor_set(v_reuseFailAlloc_1901_, 10, v_exprFVarArgs_1889_);
lean_ctor_set(v_reuseFailAlloc_1901_, 11, v_toProcess_1890_);
v___x_1896_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = lean_st_ref_put(v_a_1861_, v___x_1896_);
if (v_isShared_1877_ == 0)
{
v___x_1899_ = v___x_1876_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1874_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
else
{
lean_dec(v_a_1868_);
return v___x_1873_;
}
}
else
{
lean_object* v_val_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_a_1868_);
v_val_1904_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1872_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_val_1904_);
lean_dec(v___x_1872_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set_tag(v___x_1906_, 0);
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_val_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
else
{
return v___x_1867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_collectExpr___boxed(lean_object* v_e_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
uint8_t v_a_boxed_1923_; lean_object* v_res_1924_; 
v_a_boxed_1923_ = lean_unbox(v_a_1916_);
v_res_1924_ = l_Lean_Meta_Closure_collectExpr(v_e_1915_, v_a_boxed_1923_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec(v_a_1917_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcessAux(lean_object* v_lctx_1925_, lean_object* v_i_1926_, lean_object* v_toProcess_1927_, lean_object* v_elem_1928_){
_start:
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = lean_array_get_size(v_toProcess_1927_);
v___x_1930_ = lean_nat_dec_lt(v_i_1926_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
lean_dec(v_i_1926_);
lean_dec_ref(v_lctx_1925_);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v_elem_1928_);
lean_ctor_set(v___x_1931_, 1, v_toProcess_1927_);
return v___x_1931_;
}
else
{
lean_object* v_fvarId_1932_; lean_object* v_elem_x27_1933_; lean_object* v_fvarId_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v_fvarId_1932_ = lean_ctor_get(v_elem_1928_, 0);
v_elem_x27_1933_ = lean_array_fget_borrowed(v_toProcess_1927_, v_i_1926_);
v_fvarId_1934_ = lean_ctor_get(v_elem_x27_1933_, 0);
lean_inc(v_fvarId_1932_);
lean_inc_ref_n(v_lctx_1925_, 2);
v___x_1935_ = l_Lean_LocalContext_get_x21(v_lctx_1925_, v_fvarId_1932_);
v___x_1936_ = l_Lean_LocalDecl_index(v___x_1935_);
lean_dec_ref(v___x_1935_);
lean_inc(v_fvarId_1934_);
v___x_1937_ = l_Lean_LocalContext_get_x21(v_lctx_1925_, v_fvarId_1934_);
v___x_1938_ = l_Lean_LocalDecl_index(v___x_1937_);
lean_dec_ref(v___x_1937_);
v___x_1939_ = lean_nat_dec_lt(v___x_1936_, v___x_1938_);
lean_dec(v___x_1938_);
lean_dec(v___x_1936_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_unsigned_to_nat(1u);
v___x_1941_ = lean_nat_add(v_i_1926_, v___x_1940_);
lean_dec(v_i_1926_);
v_i_1926_ = v___x_1941_;
goto _start;
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
lean_inc(v_elem_x27_1933_);
v___x_1943_ = lean_unsigned_to_nat(1u);
v___x_1944_ = lean_nat_add(v_i_1926_, v___x_1943_);
v___x_1945_ = lean_array_fset(v_toProcess_1927_, v_i_1926_, v_elem_1928_);
lean_dec(v_i_1926_);
v_i_1926_ = v___x_1944_;
v_toProcess_1927_ = v___x_1945_;
v_elem_1928_ = v_elem_x27_1933_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_lctx_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_toProcess_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v_lctx_1950_ = lean_ctor_get(v_a_1948_, 2);
v___x_1951_ = ((lean_object*)(l_Lean_Meta_Closure_instInhabitedToProcessElement_default));
v___x_1952_ = lean_st_ref_get(v_a_1947_);
v_toProcess_1953_ = lean_ctor_get(v___x_1952_, 11);
lean_inc_ref(v_toProcess_1953_);
lean_dec(v___x_1952_);
v___x_1954_ = lean_array_get_size(v_toProcess_1953_);
lean_dec_ref(v_toProcess_1953_);
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = lean_nat_dec_eq(v___x_1954_, v___x_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v_visitedLevel_1958_; lean_object* v_visitedExpr_1959_; lean_object* v_levelParams_1960_; lean_object* v_nextLevelIdx_1961_; lean_object* v_levelArgs_1962_; lean_object* v_newLocalDecls_1963_; lean_object* v_newLocalDeclsForMVars_1964_; lean_object* v_newLetDecls_1965_; lean_object* v_nextExprIdx_1966_; lean_object* v_exprMVarArgs_1967_; lean_object* v_exprFVarArgs_1968_; lean_object* v_toProcess_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1987_; 
v___x_1957_ = lean_st_ref_take(v_a_1947_);
v_visitedLevel_1958_ = lean_ctor_get(v___x_1957_, 0);
v_visitedExpr_1959_ = lean_ctor_get(v___x_1957_, 1);
v_levelParams_1960_ = lean_ctor_get(v___x_1957_, 2);
v_nextLevelIdx_1961_ = lean_ctor_get(v___x_1957_, 3);
v_levelArgs_1962_ = lean_ctor_get(v___x_1957_, 4);
v_newLocalDecls_1963_ = lean_ctor_get(v___x_1957_, 5);
v_newLocalDeclsForMVars_1964_ = lean_ctor_get(v___x_1957_, 6);
v_newLetDecls_1965_ = lean_ctor_get(v___x_1957_, 7);
v_nextExprIdx_1966_ = lean_ctor_get(v___x_1957_, 8);
v_exprMVarArgs_1967_ = lean_ctor_get(v___x_1957_, 9);
v_exprFVarArgs_1968_ = lean_ctor_get(v___x_1957_, 10);
v_toProcess_1969_ = lean_ctor_get(v___x_1957_, 11);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1971_ = v___x_1957_;
v_isShared_1972_ = v_isSharedCheck_1987_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_toProcess_1969_);
lean_inc(v_exprFVarArgs_1968_);
lean_inc(v_exprMVarArgs_1967_);
lean_inc(v_nextExprIdx_1966_);
lean_inc(v_newLetDecls_1965_);
lean_inc(v_newLocalDeclsForMVars_1964_);
lean_inc(v_newLocalDecls_1963_);
lean_inc(v_levelArgs_1962_);
lean_inc(v_nextLevelIdx_1961_);
lean_inc(v_levelParams_1960_);
lean_inc(v_visitedExpr_1959_);
lean_inc(v_visitedLevel_1958_);
lean_dec(v___x_1957_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1987_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v_fst_1979_; lean_object* v_snd_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1973_ = lean_array_get_size(v_toProcess_1969_);
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = lean_nat_sub(v___x_1973_, v___x_1974_);
v___x_1976_ = lean_array_get(v___x_1951_, v_toProcess_1969_, v___x_1975_);
lean_dec(v___x_1975_);
v___x_1977_ = lean_array_pop(v_toProcess_1969_);
lean_inc_ref(v_lctx_1950_);
v___x_1978_ = l_Lean_Meta_Closure_pickNextToProcessAux(v_lctx_1950_, v___x_1955_, v___x_1977_, v___x_1976_);
v_fst_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_fst_1979_);
v_snd_1980_ = lean_ctor_get(v___x_1978_, 1);
lean_inc(v_snd_1980_);
lean_dec_ref(v___x_1978_);
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v_fst_1979_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 11, v_snd_1980_);
v___x_1983_ = v___x_1971_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_visitedLevel_1958_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_visitedExpr_1959_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_levelParams_1960_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_nextLevelIdx_1961_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_levelArgs_1962_);
lean_ctor_set(v_reuseFailAlloc_1986_, 5, v_newLocalDecls_1963_);
lean_ctor_set(v_reuseFailAlloc_1986_, 6, v_newLocalDeclsForMVars_1964_);
lean_ctor_set(v_reuseFailAlloc_1986_, 7, v_newLetDecls_1965_);
lean_ctor_set(v_reuseFailAlloc_1986_, 8, v_nextExprIdx_1966_);
lean_ctor_set(v_reuseFailAlloc_1986_, 9, v_exprMVarArgs_1967_);
lean_ctor_set(v_reuseFailAlloc_1986_, 10, v_exprFVarArgs_1968_);
lean_ctor_set(v_reuseFailAlloc_1986_, 11, v_snd_1980_);
v___x_1983_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_st_ref_put(v_a_1947_, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1981_);
return v___x_1985_;
}
}
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = lean_box(0);
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
return v___x_1989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg___boxed(lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1990_, v_a_1991_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f(uint8_t v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_1995_, v_a_1996_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pickNextToProcess_x3f___boxed(lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
uint8_t v_a_boxed_2009_; lean_object* v_res_2010_; 
v_a_boxed_2009_ = lean_unbox(v_a_2002_);
v_res_2010_ = l_Lean_Meta_Closure_pickNextToProcess_x3f(v_a_boxed_2009_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg(lean_object* v_e_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v___x_2014_; lean_object* v_visitedLevel_2015_; lean_object* v_visitedExpr_2016_; lean_object* v_levelParams_2017_; lean_object* v_nextLevelIdx_2018_; lean_object* v_levelArgs_2019_; lean_object* v_newLocalDecls_2020_; lean_object* v_newLocalDeclsForMVars_2021_; lean_object* v_newLetDecls_2022_; lean_object* v_nextExprIdx_2023_; lean_object* v_exprMVarArgs_2024_; lean_object* v_exprFVarArgs_2025_; lean_object* v_toProcess_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2037_; 
v___x_2014_ = lean_st_ref_take(v_a_2012_);
v_visitedLevel_2015_ = lean_ctor_get(v___x_2014_, 0);
v_visitedExpr_2016_ = lean_ctor_get(v___x_2014_, 1);
v_levelParams_2017_ = lean_ctor_get(v___x_2014_, 2);
v_nextLevelIdx_2018_ = lean_ctor_get(v___x_2014_, 3);
v_levelArgs_2019_ = lean_ctor_get(v___x_2014_, 4);
v_newLocalDecls_2020_ = lean_ctor_get(v___x_2014_, 5);
v_newLocalDeclsForMVars_2021_ = lean_ctor_get(v___x_2014_, 6);
v_newLetDecls_2022_ = lean_ctor_get(v___x_2014_, 7);
v_nextExprIdx_2023_ = lean_ctor_get(v___x_2014_, 8);
v_exprMVarArgs_2024_ = lean_ctor_get(v___x_2014_, 9);
v_exprFVarArgs_2025_ = lean_ctor_get(v___x_2014_, 10);
v_toProcess_2026_ = lean_ctor_get(v___x_2014_, 11);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2028_ = v___x_2014_;
v_isShared_2029_ = v_isSharedCheck_2037_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_toProcess_2026_);
lean_inc(v_exprFVarArgs_2025_);
lean_inc(v_exprMVarArgs_2024_);
lean_inc(v_nextExprIdx_2023_);
lean_inc(v_newLetDecls_2022_);
lean_inc(v_newLocalDeclsForMVars_2021_);
lean_inc(v_newLocalDecls_2020_);
lean_inc(v_levelArgs_2019_);
lean_inc(v_nextLevelIdx_2018_);
lean_inc(v_levelParams_2017_);
lean_inc(v_visitedExpr_2016_);
lean_inc(v_visitedLevel_2015_);
lean_dec(v___x_2014_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2037_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2030_ = lean_box(0);
v___x_2031_ = lean_array_push(v_exprFVarArgs_2025_, v_e_2011_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 10, v___x_2031_);
v___x_2033_ = v___x_2028_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_visitedLevel_2015_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_visitedExpr_2016_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_levelParams_2017_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v_nextLevelIdx_2018_);
lean_ctor_set(v_reuseFailAlloc_2036_, 4, v_levelArgs_2019_);
lean_ctor_set(v_reuseFailAlloc_2036_, 5, v_newLocalDecls_2020_);
lean_ctor_set(v_reuseFailAlloc_2036_, 6, v_newLocalDeclsForMVars_2021_);
lean_ctor_set(v_reuseFailAlloc_2036_, 7, v_newLetDecls_2022_);
lean_ctor_set(v_reuseFailAlloc_2036_, 8, v_nextExprIdx_2023_);
lean_ctor_set(v_reuseFailAlloc_2036_, 9, v_exprMVarArgs_2024_);
lean_ctor_set(v_reuseFailAlloc_2036_, 10, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2036_, 11, v_toProcess_2026_);
v___x_2033_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_st_ref_put(v_a_2012_, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2030_);
return v___x_2035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___redArg___boxed(lean_object* v_e_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2038_, v_a_2039_);
lean_dec(v_a_2039_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg(lean_object* v_e_2042_, uint8_t v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v_e_2042_, v_a_2044_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushFVarArg___boxed(lean_object* v_e_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
uint8_t v_a_boxed_2059_; lean_object* v_res_2060_; 
v_a_boxed_2059_ = lean_unbox(v_a_2052_);
v_res_2060_ = l_Lean_Meta_Closure_pushFVarArg(v_e_2051_, v_a_boxed_2059_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl(lean_object* v_newFVarId_2061_, lean_object* v_userName_2062_, lean_object* v_type_2063_, uint8_t v_bi_2064_, uint8_t v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_Meta_Closure_collectExpr(v_type_2063_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2106_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2106_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2106_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v_visitedLevel_2078_; lean_object* v_visitedExpr_2079_; lean_object* v_levelParams_2080_; lean_object* v_nextLevelIdx_2081_; lean_object* v_levelArgs_2082_; lean_object* v_newLocalDecls_2083_; lean_object* v_newLocalDeclsForMVars_2084_; lean_object* v_newLetDecls_2085_; lean_object* v_nextExprIdx_2086_; lean_object* v_exprMVarArgs_2087_; lean_object* v_exprFVarArgs_2088_; lean_object* v_toProcess_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2105_; 
v___x_2077_ = lean_st_ref_take(v_a_2066_);
v_visitedLevel_2078_ = lean_ctor_get(v___x_2077_, 0);
v_visitedExpr_2079_ = lean_ctor_get(v___x_2077_, 1);
v_levelParams_2080_ = lean_ctor_get(v___x_2077_, 2);
v_nextLevelIdx_2081_ = lean_ctor_get(v___x_2077_, 3);
v_levelArgs_2082_ = lean_ctor_get(v___x_2077_, 4);
v_newLocalDecls_2083_ = lean_ctor_get(v___x_2077_, 5);
v_newLocalDeclsForMVars_2084_ = lean_ctor_get(v___x_2077_, 6);
v_newLetDecls_2085_ = lean_ctor_get(v___x_2077_, 7);
v_nextExprIdx_2086_ = lean_ctor_get(v___x_2077_, 8);
v_exprMVarArgs_2087_ = lean_ctor_get(v___x_2077_, 9);
v_exprFVarArgs_2088_ = lean_ctor_get(v___x_2077_, 10);
v_toProcess_2089_ = lean_ctor_get(v___x_2077_, 11);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2091_ = v___x_2077_;
v_isShared_2092_ = v_isSharedCheck_2105_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_toProcess_2089_);
lean_inc(v_exprFVarArgs_2088_);
lean_inc(v_exprMVarArgs_2087_);
lean_inc(v_nextExprIdx_2086_);
lean_inc(v_newLetDecls_2085_);
lean_inc(v_newLocalDeclsForMVars_2084_);
lean_inc(v_newLocalDecls_2083_);
lean_inc(v_levelArgs_2082_);
lean_inc(v_nextLevelIdx_2081_);
lean_inc(v_levelParams_2080_);
lean_inc(v_visitedExpr_2079_);
lean_inc(v_visitedLevel_2078_);
lean_dec(v___x_2077_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2105_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = 0;
v___x_2096_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v_newFVarId_2061_);
lean_ctor_set(v___x_2096_, 2, v_userName_2062_);
lean_ctor_set(v___x_2096_, 3, v_a_2073_);
lean_ctor_set_uint8(v___x_2096_, sizeof(void*)*4, v_bi_2064_);
lean_ctor_set_uint8(v___x_2096_, sizeof(void*)*4 + 1, v___x_2095_);
v___x_2097_ = lean_array_push(v_newLocalDecls_2083_, v___x_2096_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 5, v___x_2097_);
v___x_2099_ = v___x_2091_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_visitedLevel_2078_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_visitedExpr_2079_);
lean_ctor_set(v_reuseFailAlloc_2104_, 2, v_levelParams_2080_);
lean_ctor_set(v_reuseFailAlloc_2104_, 3, v_nextLevelIdx_2081_);
lean_ctor_set(v_reuseFailAlloc_2104_, 4, v_levelArgs_2082_);
lean_ctor_set(v_reuseFailAlloc_2104_, 5, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2104_, 6, v_newLocalDeclsForMVars_2084_);
lean_ctor_set(v_reuseFailAlloc_2104_, 7, v_newLetDecls_2085_);
lean_ctor_set(v_reuseFailAlloc_2104_, 8, v_nextExprIdx_2086_);
lean_ctor_set(v_reuseFailAlloc_2104_, 9, v_exprMVarArgs_2087_);
lean_ctor_set(v_reuseFailAlloc_2104_, 10, v_exprFVarArgs_2088_);
lean_ctor_set(v_reuseFailAlloc_2104_, 11, v_toProcess_2089_);
v___x_2099_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2100_ = lean_st_ref_put(v_a_2066_, v___x_2099_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2093_);
v___x_2102_ = v___x_2075_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2093_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec(v_userName_2062_);
lean_dec(v_newFVarId_2061_);
v_a_2107_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2072_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2072_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_pushLocalDecl___boxed(lean_object* v_newFVarId_2115_, lean_object* v_userName_2116_, lean_object* v_type_2117_, lean_object* v_bi_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
uint8_t v_bi_boxed_2126_; uint8_t v_a_boxed_2127_; lean_object* v_res_2128_; 
v_bi_boxed_2126_ = lean_unbox(v_bi_2118_);
v_a_boxed_2127_ = lean_unbox(v_a_2119_);
v_res_2128_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2115_, v_userName_2116_, v_type_2117_, v_bi_boxed_2126_, v_a_boxed_2127_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_a_2120_);
return v_res_2128_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(lean_object* v_k_2129_, lean_object* v_t_2130_){
_start:
{
if (lean_obj_tag(v_t_2130_) == 0)
{
lean_object* v_k_2131_; lean_object* v_l_2132_; lean_object* v_r_2133_; uint8_t v___x_2134_; 
v_k_2131_ = lean_ctor_get(v_t_2130_, 1);
v_l_2132_ = lean_ctor_get(v_t_2130_, 3);
v_r_2133_ = lean_ctor_get(v_t_2130_, 4);
v___x_2134_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2129_, v_k_2131_);
switch(v___x_2134_)
{
case 0:
{
v_t_2130_ = v_l_2132_;
goto _start;
}
case 1:
{
uint8_t v___x_2136_; 
v___x_2136_ = 1;
return v___x_2136_;
}
default: 
{
v_t_2130_ = v_r_2133_;
goto _start;
}
}
}
else
{
uint8_t v___x_2138_; 
v___x_2138_ = 0;
return v___x_2138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg___boxed(lean_object* v_k_2139_, lean_object* v_t_2140_){
_start:
{
uint8_t v_res_2141_; lean_object* v_r_2142_; 
v_res_2141_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2139_, v_t_2140_);
lean_dec(v_t_2140_);
lean_dec(v_k_2139_);
v_r_2142_ = lean_box(v_res_2141_);
return v_r_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(lean_object* v_newFVarId_2143_, lean_object* v_a_2144_, size_t v_sz_2145_, size_t v_i_2146_, lean_object* v_bs_2147_){
_start:
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_usize_dec_lt(v_i_2146_, v_sz_2145_);
if (v___x_2148_ == 0)
{
lean_dec(v_newFVarId_2143_);
return v_bs_2147_;
}
else
{
lean_object* v_v_2149_; lean_object* v___x_2150_; lean_object* v_bs_x27_2151_; lean_object* v___x_2152_; size_t v___x_2153_; size_t v___x_2154_; lean_object* v___x_2155_; 
v_v_2149_ = lean_array_uget(v_bs_2147_, v_i_2146_);
v___x_2150_ = lean_unsigned_to_nat(0u);
v_bs_x27_2151_ = lean_array_uset(v_bs_2147_, v_i_2146_, v___x_2150_);
lean_inc(v_newFVarId_2143_);
v___x_2152_ = l_Lean_LocalDecl_replaceFVarId(v_newFVarId_2143_, v_a_2144_, v_v_2149_);
v___x_2153_ = ((size_t)1ULL);
v___x_2154_ = lean_usize_add(v_i_2146_, v___x_2153_);
v___x_2155_ = lean_array_uset(v_bs_x27_2151_, v_i_2146_, v___x_2152_);
v_i_2146_ = v___x_2154_;
v_bs_2147_ = v___x_2155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1___boxed(lean_object* v_newFVarId_2157_, lean_object* v_a_2158_, lean_object* v_sz_2159_, lean_object* v_i_2160_, lean_object* v_bs_2161_){
_start:
{
size_t v_sz_boxed_2162_; size_t v_i_boxed_2163_; lean_object* v_res_2164_; 
v_sz_boxed_2162_ = lean_unbox_usize(v_sz_2159_);
lean_dec(v_sz_2159_);
v_i_boxed_2163_ = lean_unbox_usize(v_i_2160_);
lean_dec(v_i_2160_);
v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2157_, v_a_2158_, v_sz_boxed_2162_, v_i_boxed_2163_, v_bs_2161_);
lean_dec_ref(v_a_2158_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process(uint8_t v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Meta_Closure_pickNextToProcess_x3f___redArg(v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2300_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2300_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2300_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
if (lean_obj_tag(v_a_2173_) == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2177_ = lean_box(0);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2177_);
v___x_2179_ = v___x_2175_;
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
lean_object* v_val_2181_; lean_object* v_fvarId_2182_; lean_object* v_newFVarId_2183_; lean_object* v___x_2184_; 
lean_del_object(v___x_2175_);
v_val_2181_ = lean_ctor_get(v_a_2173_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v_a_2173_, 1);
v_fvarId_2182_ = lean_ctor_get(v_val_2181_, 0);
lean_inc_n(v_fvarId_2182_, 2);
v_newFVarId_2183_ = lean_ctor_get(v_val_2181_, 1);
lean_inc(v_newFVarId_2183_);
lean_dec(v_val_2181_);
v___x_2184_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_2182_, v_a_2167_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
if (lean_obj_tag(v_a_2185_) == 0)
{
lean_object* v_userName_2186_; lean_object* v_type_2187_; uint8_t v_bi_2188_; lean_object* v___x_2189_; 
v_userName_2186_ = lean_ctor_get(v_a_2185_, 2);
lean_inc(v_userName_2186_);
v_type_2187_ = lean_ctor_get(v_a_2185_, 3);
lean_inc_ref(v_type_2187_);
v_bi_2188_ = lean_ctor_get_uint8(v_a_2185_, sizeof(void*)*4);
lean_dec_ref_known(v_a_2185_, 4);
v___x_2189_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2183_, v_userName_2186_, v_type_2187_, v_bi_2188_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec_ref_known(v___x_2189_, 1);
v___x_2190_ = l_Lean_mkFVar(v_fvarId_2182_);
v___x_2191_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2190_, v_a_2166_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_dec_ref_known(v___x_2191_, 1);
goto _start;
}
else
{
return v___x_2191_;
}
}
else
{
lean_dec(v_fvarId_2182_);
return v___x_2189_;
}
}
else
{
lean_object* v_userName_2193_; lean_object* v_type_2194_; lean_object* v_value_2195_; uint8_t v_nondep_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2289_; 
v_userName_2193_ = lean_ctor_get(v_a_2185_, 2);
v_type_2194_ = lean_ctor_get(v_a_2185_, 3);
v_value_2195_ = lean_ctor_get(v_a_2185_, 4);
v_nondep_2196_ = lean_ctor_get_uint8(v_a_2185_, sizeof(void*)*5);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_a_2185_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; lean_object* v_unused_2291_; 
v_unused_2290_ = lean_ctor_get(v_a_2185_, 1);
lean_dec(v_unused_2290_);
v_unused_2291_ = lean_ctor_get(v_a_2185_, 0);
lean_dec(v_unused_2291_);
v___x_2198_ = v_a_2185_;
v_isShared_2199_ = v_isSharedCheck_2289_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_value_2195_);
lean_inc(v_type_2194_);
lean_inc(v_userName_2193_);
lean_dec(v_a_2185_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2289_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v_a_2168_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2200_, 1);
if (v_nondep_2196_ == 0)
{
uint8_t v___x_2208_; 
v___x_2208_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_fvarId_2182_, v_a_2201_);
lean_dec(v_a_2201_);
if (v___x_2208_ == 0)
{
lean_del_object(v___x_2198_);
lean_dec_ref(v_value_2195_);
goto v___jp_2202_;
}
else
{
lean_object* v___x_2209_; 
lean_dec(v_fvarId_2182_);
v___x_2209_ = l_Lean_Meta_Closure_collectExpr(v_type_2194_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2211_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v___x_2211_ = l_Lean_Meta_Closure_collectExpr(v_value_2195_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2213_; lean_object* v_visitedLevel_2214_; lean_object* v_visitedExpr_2215_; lean_object* v_levelParams_2216_; lean_object* v_nextLevelIdx_2217_; lean_object* v_levelArgs_2218_; lean_object* v_newLocalDecls_2219_; lean_object* v_newLocalDeclsForMVars_2220_; lean_object* v_newLetDecls_2221_; lean_object* v_nextExprIdx_2222_; lean_object* v_exprMVarArgs_2223_; lean_object* v_exprFVarArgs_2224_; lean_object* v_toProcess_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2264_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref_known(v___x_2211_, 1);
v___x_2213_ = lean_st_ref_take(v_a_2166_);
v_visitedLevel_2214_ = lean_ctor_get(v___x_2213_, 0);
v_visitedExpr_2215_ = lean_ctor_get(v___x_2213_, 1);
v_levelParams_2216_ = lean_ctor_get(v___x_2213_, 2);
v_nextLevelIdx_2217_ = lean_ctor_get(v___x_2213_, 3);
v_levelArgs_2218_ = lean_ctor_get(v___x_2213_, 4);
v_newLocalDecls_2219_ = lean_ctor_get(v___x_2213_, 5);
v_newLocalDeclsForMVars_2220_ = lean_ctor_get(v___x_2213_, 6);
v_newLetDecls_2221_ = lean_ctor_get(v___x_2213_, 7);
v_nextExprIdx_2222_ = lean_ctor_get(v___x_2213_, 8);
v_exprMVarArgs_2223_ = lean_ctor_get(v___x_2213_, 9);
v_exprFVarArgs_2224_ = lean_ctor_get(v___x_2213_, 10);
v_toProcess_2225_ = lean_ctor_get(v___x_2213_, 11);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2227_ = v___x_2213_;
v_isShared_2228_ = v_isSharedCheck_2264_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_toProcess_2225_);
lean_inc(v_exprFVarArgs_2224_);
lean_inc(v_exprMVarArgs_2223_);
lean_inc(v_nextExprIdx_2222_);
lean_inc(v_newLetDecls_2221_);
lean_inc(v_newLocalDeclsForMVars_2220_);
lean_inc(v_newLocalDecls_2219_);
lean_inc(v_levelArgs_2218_);
lean_inc(v_nextLevelIdx_2217_);
lean_inc(v_levelParams_2216_);
lean_inc(v_visitedExpr_2215_);
lean_inc(v_visitedLevel_2214_);
lean_dec(v___x_2213_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2264_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; uint8_t v___x_2230_; lean_object* v___x_2232_; 
v___x_2229_ = lean_unsigned_to_nat(0u);
v___x_2230_ = 0;
lean_inc(v_a_2212_);
lean_inc(v_newFVarId_2183_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 4, v_a_2212_);
lean_ctor_set(v___x_2198_, 3, v_a_2210_);
lean_ctor_set(v___x_2198_, 1, v_newFVarId_2183_);
lean_ctor_set(v___x_2198_, 0, v___x_2229_);
v___x_2232_ = v___x_2198_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_newFVarId_2183_);
lean_ctor_set(v_reuseFailAlloc_2263_, 2, v_userName_2193_);
lean_ctor_set(v_reuseFailAlloc_2263_, 3, v_a_2210_);
lean_ctor_set(v_reuseFailAlloc_2263_, 4, v_a_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2263_, sizeof(void*)*5, v_nondep_2196_);
v___x_2232_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2235_; 
lean_ctor_set_uint8(v___x_2232_, sizeof(void*)*5 + 1, v___x_2230_);
v___x_2233_ = lean_array_push(v_newLetDecls_2221_, v___x_2232_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 7, v___x_2233_);
v___x_2235_ = v___x_2227_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_visitedLevel_2214_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_visitedExpr_2215_);
lean_ctor_set(v_reuseFailAlloc_2262_, 2, v_levelParams_2216_);
lean_ctor_set(v_reuseFailAlloc_2262_, 3, v_nextLevelIdx_2217_);
lean_ctor_set(v_reuseFailAlloc_2262_, 4, v_levelArgs_2218_);
lean_ctor_set(v_reuseFailAlloc_2262_, 5, v_newLocalDecls_2219_);
lean_ctor_set(v_reuseFailAlloc_2262_, 6, v_newLocalDeclsForMVars_2220_);
lean_ctor_set(v_reuseFailAlloc_2262_, 7, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2262_, 8, v_nextExprIdx_2222_);
lean_ctor_set(v_reuseFailAlloc_2262_, 9, v_exprMVarArgs_2223_);
lean_ctor_set(v_reuseFailAlloc_2262_, 10, v_exprFVarArgs_2224_);
lean_ctor_set(v_reuseFailAlloc_2262_, 11, v_toProcess_2225_);
v___x_2235_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v_visitedLevel_2238_; lean_object* v_visitedExpr_2239_; lean_object* v_levelParams_2240_; lean_object* v_nextLevelIdx_2241_; lean_object* v_levelArgs_2242_; lean_object* v_newLocalDecls_2243_; lean_object* v_newLocalDeclsForMVars_2244_; lean_object* v_newLetDecls_2245_; lean_object* v_nextExprIdx_2246_; lean_object* v_exprMVarArgs_2247_; lean_object* v_exprFVarArgs_2248_; lean_object* v_toProcess_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2261_; 
v___x_2236_ = lean_st_ref_put(v_a_2166_, v___x_2235_);
v___x_2237_ = lean_st_ref_take(v_a_2166_);
v_visitedLevel_2238_ = lean_ctor_get(v___x_2237_, 0);
v_visitedExpr_2239_ = lean_ctor_get(v___x_2237_, 1);
v_levelParams_2240_ = lean_ctor_get(v___x_2237_, 2);
v_nextLevelIdx_2241_ = lean_ctor_get(v___x_2237_, 3);
v_levelArgs_2242_ = lean_ctor_get(v___x_2237_, 4);
v_newLocalDecls_2243_ = lean_ctor_get(v___x_2237_, 5);
v_newLocalDeclsForMVars_2244_ = lean_ctor_get(v___x_2237_, 6);
v_newLetDecls_2245_ = lean_ctor_get(v___x_2237_, 7);
v_nextExprIdx_2246_ = lean_ctor_get(v___x_2237_, 8);
v_exprMVarArgs_2247_ = lean_ctor_get(v___x_2237_, 9);
v_exprFVarArgs_2248_ = lean_ctor_get(v___x_2237_, 10);
v_toProcess_2249_ = lean_ctor_get(v___x_2237_, 11);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2251_ = v___x_2237_;
v_isShared_2252_ = v_isSharedCheck_2261_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_toProcess_2249_);
lean_inc(v_exprFVarArgs_2248_);
lean_inc(v_exprMVarArgs_2247_);
lean_inc(v_nextExprIdx_2246_);
lean_inc(v_newLetDecls_2245_);
lean_inc(v_newLocalDeclsForMVars_2244_);
lean_inc(v_newLocalDecls_2243_);
lean_inc(v_levelArgs_2242_);
lean_inc(v_nextLevelIdx_2241_);
lean_inc(v_levelParams_2240_);
lean_inc(v_visitedExpr_2239_);
lean_inc(v_visitedLevel_2238_);
lean_dec(v___x_2237_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2261_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
size_t v_sz_2253_; size_t v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2257_; 
v_sz_2253_ = lean_array_size(v_newLocalDecls_2243_);
v___x_2254_ = ((size_t)0ULL);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_process_spec__1(v_newFVarId_2183_, v_a_2212_, v_sz_2253_, v___x_2254_, v_newLocalDecls_2243_);
lean_dec(v_a_2212_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 5, v___x_2255_);
v___x_2257_ = v___x_2251_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_visitedLevel_2238_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_visitedExpr_2239_);
lean_ctor_set(v_reuseFailAlloc_2260_, 2, v_levelParams_2240_);
lean_ctor_set(v_reuseFailAlloc_2260_, 3, v_nextLevelIdx_2241_);
lean_ctor_set(v_reuseFailAlloc_2260_, 4, v_levelArgs_2242_);
lean_ctor_set(v_reuseFailAlloc_2260_, 5, v___x_2255_);
lean_ctor_set(v_reuseFailAlloc_2260_, 6, v_newLocalDeclsForMVars_2244_);
lean_ctor_set(v_reuseFailAlloc_2260_, 7, v_newLetDecls_2245_);
lean_ctor_set(v_reuseFailAlloc_2260_, 8, v_nextExprIdx_2246_);
lean_ctor_set(v_reuseFailAlloc_2260_, 9, v_exprMVarArgs_2247_);
lean_ctor_set(v_reuseFailAlloc_2260_, 10, v_exprFVarArgs_2248_);
lean_ctor_set(v_reuseFailAlloc_2260_, 11, v_toProcess_2249_);
v___x_2257_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_st_ref_put(v_a_2166_, v___x_2257_);
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_a_2210_);
lean_del_object(v___x_2198_);
lean_dec(v_userName_2193_);
lean_dec(v_newFVarId_2183_);
v_a_2265_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2211_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2211_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_del_object(v___x_2198_);
lean_dec_ref(v_value_2195_);
lean_dec(v_userName_2193_);
lean_dec(v_newFVarId_2183_);
v_a_2273_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2209_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2209_);
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
else
{
lean_dec(v_a_2201_);
lean_del_object(v___x_2198_);
lean_dec_ref(v_value_2195_);
goto v___jp_2202_;
}
v___jp_2202_:
{
uint8_t v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = 0;
v___x_2204_ = l_Lean_Meta_Closure_pushLocalDecl(v_newFVarId_2183_, v_userName_2193_, v_type_2194_, v___x_2203_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec_ref_known(v___x_2204_, 1);
v___x_2205_ = l_Lean_mkFVar(v_fvarId_2182_);
v___x_2206_ = l_Lean_Meta_Closure_pushFVarArg___redArg(v___x_2205_, v_a_2166_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_dec_ref_known(v___x_2206_, 1);
goto _start;
}
else
{
return v___x_2206_;
}
}
else
{
lean_dec(v_fvarId_2182_);
return v___x_2204_;
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_del_object(v___x_2198_);
lean_dec_ref(v_value_2195_);
lean_dec_ref(v_type_2194_);
lean_dec(v_userName_2193_);
lean_dec(v_newFVarId_2183_);
lean_dec(v_fvarId_2182_);
v_a_2281_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2200_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2200_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_newFVarId_2183_);
lean_dec(v_fvarId_2182_);
v_a_2292_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2184_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2184_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
v_a_2301_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2172_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2172_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_process___boxed(lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
uint8_t v_a_boxed_2316_; lean_object* v_res_2317_; 
v_a_boxed_2316_ = lean_unbox(v_a_2309_);
v_res_2317_ = l_Lean_Meta_Closure_process(v_a_boxed_2316_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
return v_res_2317_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(lean_object* v_00_u03b2_2318_, lean_object* v_k_2319_, lean_object* v_t_2320_){
_start:
{
uint8_t v___x_2321_; 
v___x_2321_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___redArg(v_k_2319_, v_t_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0___boxed(lean_object* v_00_u03b2_2322_, lean_object* v_k_2323_, lean_object* v_t_2324_){
_start:
{
uint8_t v_res_2325_; lean_object* v_r_2326_; 
v_res_2325_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Closure_process_spec__0(v_00_u03b2_2322_, v_k_2323_, v_t_2324_);
lean_dec(v_t_2324_);
lean_dec(v_k_2323_);
v_r_2326_ = lean_box(v_res_2325_);
return v_r_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0(lean_object* v_decls_2327_, lean_object* v_xs_2328_, uint8_t v_isLambda_2329_, lean_object* v_i_2330_, lean_object* v_x_2331_, lean_object* v_b_2332_){
_start:
{
lean_object* v_decl_2333_; 
v_decl_2333_ = lean_array_fget_borrowed(v_decls_2327_, v_i_2330_);
if (lean_obj_tag(v_decl_2333_) == 0)
{
lean_object* v_userName_2334_; lean_object* v_type_2335_; uint8_t v_bi_2336_; lean_object* v_ty_2337_; 
v_userName_2334_ = lean_ctor_get(v_decl_2333_, 2);
v_type_2335_ = lean_ctor_get(v_decl_2333_, 3);
v_bi_2336_ = lean_ctor_get_uint8(v_decl_2333_, sizeof(void*)*4);
v_ty_2337_ = lean_expr_abstract_range(v_type_2335_, v_i_2330_, v_xs_2328_);
if (v_isLambda_2329_ == 0)
{
lean_object* v___x_2338_; 
lean_inc(v_userName_2334_);
v___x_2338_ = l_Lean_mkForall(v_userName_2334_, v_bi_2336_, v_ty_2337_, v_b_2332_);
return v___x_2338_;
}
else
{
lean_object* v___x_2339_; 
lean_inc(v_userName_2334_);
v___x_2339_ = l_Lean_mkLambda(v_userName_2334_, v_bi_2336_, v_ty_2337_, v_b_2332_);
return v___x_2339_;
}
}
else
{
lean_object* v_userName_2340_; lean_object* v_type_2341_; lean_object* v_value_2342_; uint8_t v_nondep_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v_userName_2340_ = lean_ctor_get(v_decl_2333_, 2);
v_type_2341_ = lean_ctor_get(v_decl_2333_, 3);
v_value_2342_ = lean_ctor_get(v_decl_2333_, 4);
v_nondep_2343_ = lean_ctor_get_uint8(v_decl_2333_, sizeof(void*)*5);
v___x_2344_ = lean_unsigned_to_nat(0u);
v___x_2345_ = lean_expr_has_loose_bvar(v_b_2332_, v___x_2344_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_unsigned_to_nat(1u);
v___x_2347_ = lean_expr_lower_loose_bvars(v_b_2332_, v___x_2346_, v___x_2346_);
lean_dec_ref(v_b_2332_);
return v___x_2347_;
}
else
{
lean_object* v_ty_2348_; lean_object* v_val_2349_; lean_object* v___x_2350_; 
v_ty_2348_ = lean_expr_abstract_range(v_type_2341_, v_i_2330_, v_xs_2328_);
v_val_2349_ = lean_expr_abstract_range(v_value_2342_, v_i_2330_, v_xs_2328_);
lean_inc(v_userName_2340_);
v___x_2350_ = l_Lean_Expr_letE___override(v_userName_2340_, v_ty_2348_, v_val_2349_, v_b_2332_, v_nondep_2343_);
return v___x_2350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___lam__0___boxed(lean_object* v_decls_2351_, lean_object* v_xs_2352_, lean_object* v_isLambda_2353_, lean_object* v_i_2354_, lean_object* v_x_2355_, lean_object* v_b_2356_){
_start:
{
uint8_t v_isLambda_boxed_2357_; lean_object* v_res_2358_; 
v_isLambda_boxed_2357_ = lean_unbox(v_isLambda_2353_);
v_res_2358_ = l_Lean_Meta_Closure_mkBinding___lam__0(v_decls_2351_, v_xs_2352_, v_isLambda_boxed_2357_, v_i_2354_, v_x_2355_, v_b_2356_);
lean_dec(v_i_2354_);
lean_dec_ref(v_xs_2352_);
lean_dec_ref(v_decls_2351_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding(uint8_t v_isLambda_2379_, lean_object* v_decls_2380_, lean_object* v_b_2381_){
_start:
{
lean_object* v___f_2382_; lean_object* v___x_2383_; size_t v_sz_2384_; size_t v___x_2385_; lean_object* v_xs_2386_; lean_object* v___x_2387_; lean_object* v___f_2388_; lean_object* v_b_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___f_2382_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__0));
v___x_2383_ = ((lean_object*)(l_Lean_Meta_Closure_mkBinding___closed__10));
v_sz_2384_ = lean_array_size(v_decls_2380_);
v___x_2385_ = ((size_t)0ULL);
lean_inc_ref_n(v_decls_2380_, 2);
v_xs_2386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2383_, v___f_2382_, v_sz_2384_, v___x_2385_, v_decls_2380_);
v___x_2387_ = lean_box(v_isLambda_2379_);
lean_inc(v_xs_2386_);
v___f_2388_ = lean_alloc_closure((void*)(l_Lean_Meta_Closure_mkBinding___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2388_, 0, v_decls_2380_);
lean_closure_set(v___f_2388_, 1, v_xs_2386_);
lean_closure_set(v___f_2388_, 2, v___x_2387_);
v_b_2389_ = lean_expr_abstract(v_b_2381_, v_xs_2386_);
lean_dec(v_xs_2386_);
v___x_2390_ = lean_array_get_size(v_decls_2380_);
lean_dec_ref(v_decls_2380_);
v___x_2391_ = l_Nat_foldRev___redArg(v___x_2390_, v___f_2388_, v_b_2389_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkBinding___boxed(lean_object* v_isLambda_2392_, lean_object* v_decls_2393_, lean_object* v_b_2394_){
_start:
{
uint8_t v_isLambda_boxed_2395_; lean_object* v_res_2396_; 
v_isLambda_boxed_2395_ = lean_unbox(v_isLambda_2392_);
v_res_2396_ = l_Lean_Meta_Closure_mkBinding(v_isLambda_boxed_2395_, v_decls_2393_, v_b_2394_);
lean_dec_ref(v_b_2394_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(size_t v_sz_2397_, size_t v_i_2398_, lean_object* v_bs_2399_){
_start:
{
uint8_t v___x_2400_; 
v___x_2400_ = lean_usize_dec_lt(v_i_2398_, v_sz_2397_);
if (v___x_2400_ == 0)
{
return v_bs_2399_;
}
else
{
lean_object* v_v_2401_; lean_object* v___x_2402_; lean_object* v_bs_x27_2403_; lean_object* v___x_2404_; size_t v___x_2405_; size_t v___x_2406_; lean_object* v___x_2407_; 
v_v_2401_ = lean_array_uget(v_bs_2399_, v_i_2398_);
v___x_2402_ = lean_unsigned_to_nat(0u);
v_bs_x27_2403_ = lean_array_uset(v_bs_2399_, v_i_2398_, v___x_2402_);
v___x_2404_ = l_Lean_LocalDecl_toExpr(v_v_2401_);
v___x_2405_ = ((size_t)1ULL);
v___x_2406_ = lean_usize_add(v_i_2398_, v___x_2405_);
v___x_2407_ = lean_array_uset(v_bs_x27_2403_, v_i_2398_, v___x_2404_);
v_i_2398_ = v___x_2406_;
v_bs_2399_ = v___x_2407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0___boxed(lean_object* v_sz_2409_, lean_object* v_i_2410_, lean_object* v_bs_2411_){
_start:
{
size_t v_sz_boxed_2412_; size_t v_i_boxed_2413_; lean_object* v_res_2414_; 
v_sz_boxed_2412_ = lean_unbox_usize(v_sz_2409_);
lean_dec(v_sz_2409_);
v_i_boxed_2413_ = lean_unbox_usize(v_i_2410_);
lean_dec(v_i_2410_);
v_res_2414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_boxed_2412_, v_i_boxed_2413_, v_bs_2411_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(lean_object* v_decls_2415_, lean_object* v_xs_2416_, lean_object* v_x_2417_, lean_object* v_x_2418_){
_start:
{
lean_object* v_zero_2419_; uint8_t v_isZero_2420_; 
v_zero_2419_ = lean_unsigned_to_nat(0u);
v_isZero_2420_ = lean_nat_dec_eq(v_x_2417_, v_zero_2419_);
if (v_isZero_2420_ == 1)
{
lean_dec(v_x_2417_);
return v_x_2418_;
}
else
{
lean_object* v_one_2421_; lean_object* v_n_2422_; lean_object* v_decl_2423_; 
v_one_2421_ = lean_unsigned_to_nat(1u);
v_n_2422_ = lean_nat_sub(v_x_2417_, v_one_2421_);
lean_dec(v_x_2417_);
v_decl_2423_ = lean_array_fget_borrowed(v_decls_2415_, v_n_2422_);
if (lean_obj_tag(v_decl_2423_) == 0)
{
lean_object* v_userName_2424_; lean_object* v_type_2425_; uint8_t v_bi_2426_; lean_object* v_ty_2427_; lean_object* v___x_2428_; 
v_userName_2424_ = lean_ctor_get(v_decl_2423_, 2);
v_type_2425_ = lean_ctor_get(v_decl_2423_, 3);
v_bi_2426_ = lean_ctor_get_uint8(v_decl_2423_, sizeof(void*)*4);
v_ty_2427_ = lean_expr_abstract_range(v_type_2425_, v_n_2422_, v_xs_2416_);
lean_inc(v_userName_2424_);
v___x_2428_ = l_Lean_mkLambda(v_userName_2424_, v_bi_2426_, v_ty_2427_, v_x_2418_);
v_x_2417_ = v_n_2422_;
v_x_2418_ = v___x_2428_;
goto _start;
}
else
{
lean_object* v_userName_2430_; lean_object* v_type_2431_; lean_object* v_value_2432_; uint8_t v_nondep_2433_; uint8_t v___x_2434_; 
v_userName_2430_ = lean_ctor_get(v_decl_2423_, 2);
v_type_2431_ = lean_ctor_get(v_decl_2423_, 3);
v_value_2432_ = lean_ctor_get(v_decl_2423_, 4);
v_nondep_2433_ = lean_ctor_get_uint8(v_decl_2423_, sizeof(void*)*5);
v___x_2434_ = lean_expr_has_loose_bvar(v_x_2418_, v_zero_2419_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_expr_lower_loose_bvars(v_x_2418_, v_one_2421_, v_one_2421_);
lean_dec_ref(v_x_2418_);
v_x_2417_ = v_n_2422_;
v_x_2418_ = v___x_2435_;
goto _start;
}
else
{
lean_object* v_ty_2437_; lean_object* v_val_2438_; lean_object* v___x_2439_; 
v_ty_2437_ = lean_expr_abstract_range(v_type_2431_, v_n_2422_, v_xs_2416_);
v_val_2438_ = lean_expr_abstract_range(v_value_2432_, v_n_2422_, v_xs_2416_);
lean_inc(v_userName_2430_);
v___x_2439_ = l_Lean_Expr_letE___override(v_userName_2430_, v_ty_2437_, v_val_2438_, v_x_2418_, v_nondep_2433_);
v_x_2417_ = v_n_2422_;
v_x_2418_ = v___x_2439_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1___boxed(lean_object* v_decls_2441_, lean_object* v_xs_2442_, lean_object* v_x_2443_, lean_object* v_x_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2441_, v_xs_2442_, v_x_2443_, v_x_2444_);
lean_dec_ref(v_xs_2442_);
lean_dec_ref(v_decls_2441_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(lean_object* v_decls_2446_, lean_object* v_xs_2447_, lean_object* v_x_2448_, lean_object* v_x_2449_){
_start:
{
lean_object* v_zero_2450_; uint8_t v_isZero_2451_; 
v_zero_2450_ = lean_unsigned_to_nat(0u);
v_isZero_2451_ = lean_nat_dec_eq(v_x_2448_, v_zero_2450_);
if (v_isZero_2451_ == 1)
{
return v_x_2449_;
}
else
{
lean_object* v_one_2452_; lean_object* v_n_2453_; lean_object* v_decl_2454_; 
v_one_2452_ = lean_unsigned_to_nat(1u);
v_n_2453_ = lean_nat_sub(v_x_2448_, v_one_2452_);
v_decl_2454_ = lean_array_fget_borrowed(v_decls_2446_, v_n_2453_);
if (lean_obj_tag(v_decl_2454_) == 0)
{
lean_object* v_userName_2455_; lean_object* v_type_2456_; uint8_t v_bi_2457_; lean_object* v_ty_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_userName_2455_ = lean_ctor_get(v_decl_2454_, 2);
v_type_2456_ = lean_ctor_get(v_decl_2454_, 3);
v_bi_2457_ = lean_ctor_get_uint8(v_decl_2454_, sizeof(void*)*4);
v_ty_2458_ = lean_expr_abstract_range(v_type_2456_, v_n_2453_, v_xs_2447_);
lean_inc(v_userName_2455_);
v___x_2459_ = l_Lean_mkLambda(v_userName_2455_, v_bi_2457_, v_ty_2458_, v_x_2449_);
v___x_2460_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2446_, v_xs_2447_, v_n_2453_, v___x_2459_);
return v___x_2460_;
}
else
{
lean_object* v_userName_2461_; lean_object* v_type_2462_; lean_object* v_value_2463_; uint8_t v_nondep_2464_; uint8_t v___x_2465_; 
v_userName_2461_ = lean_ctor_get(v_decl_2454_, 2);
v_type_2462_ = lean_ctor_get(v_decl_2454_, 3);
v_value_2463_ = lean_ctor_get(v_decl_2454_, 4);
v_nondep_2464_ = lean_ctor_get_uint8(v_decl_2454_, sizeof(void*)*5);
v___x_2465_ = lean_expr_has_loose_bvar(v_x_2449_, v_zero_2450_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = lean_expr_lower_loose_bvars(v_x_2449_, v_one_2452_, v_one_2452_);
lean_dec_ref(v_x_2449_);
v___x_2467_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2446_, v_xs_2447_, v_n_2453_, v___x_2466_);
return v___x_2467_;
}
else
{
lean_object* v_ty_2468_; lean_object* v_val_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_ty_2468_ = lean_expr_abstract_range(v_type_2462_, v_n_2453_, v_xs_2447_);
v_val_2469_ = lean_expr_abstract_range(v_value_2463_, v_n_2453_, v_xs_2447_);
lean_inc(v_userName_2461_);
v___x_2470_ = l_Lean_Expr_letE___override(v_userName_2461_, v_ty_2468_, v_val_2469_, v_x_2449_, v_nondep_2464_);
v___x_2471_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1_spec__1(v_decls_2446_, v_xs_2447_, v_n_2453_, v___x_2470_);
return v___x_2471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1___boxed(lean_object* v_decls_2472_, lean_object* v_xs_2473_, lean_object* v_x_2474_, lean_object* v_x_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2472_, v_xs_2473_, v_x_2474_, v_x_2475_);
lean_dec(v_x_2474_);
lean_dec_ref(v_xs_2473_);
lean_dec_ref(v_decls_2472_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda(lean_object* v_decls_2477_, lean_object* v_b_2478_){
_start:
{
size_t v_sz_2479_; size_t v___x_2480_; lean_object* v_xs_2481_; lean_object* v_b_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_sz_2479_ = lean_array_size(v_decls_2477_);
v___x_2480_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2477_);
v_xs_2481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2479_, v___x_2480_, v_decls_2477_);
v_b_2482_ = lean_expr_abstract(v_b_2478_, v_xs_2481_);
v___x_2483_ = lean_array_get_size(v_decls_2477_);
v___x_2484_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkLambda_spec__1(v_decls_2477_, v_xs_2481_, v___x_2483_, v_b_2482_);
lean_dec_ref(v_xs_2481_);
lean_dec_ref(v_decls_2477_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkLambda___boxed(lean_object* v_decls_2485_, lean_object* v_b_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_Meta_Closure_mkLambda(v_decls_2485_, v_b_2486_);
lean_dec_ref(v_b_2486_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(lean_object* v_decls_2488_, lean_object* v_xs_2489_, lean_object* v_x_2490_, lean_object* v_x_2491_){
_start:
{
lean_object* v_zero_2492_; uint8_t v_isZero_2493_; 
v_zero_2492_ = lean_unsigned_to_nat(0u);
v_isZero_2493_ = lean_nat_dec_eq(v_x_2490_, v_zero_2492_);
if (v_isZero_2493_ == 1)
{
lean_dec(v_x_2490_);
return v_x_2491_;
}
else
{
lean_object* v_one_2494_; lean_object* v_n_2495_; lean_object* v_decl_2496_; 
v_one_2494_ = lean_unsigned_to_nat(1u);
v_n_2495_ = lean_nat_sub(v_x_2490_, v_one_2494_);
lean_dec(v_x_2490_);
v_decl_2496_ = lean_array_fget_borrowed(v_decls_2488_, v_n_2495_);
if (lean_obj_tag(v_decl_2496_) == 0)
{
lean_object* v_userName_2497_; lean_object* v_type_2498_; uint8_t v_bi_2499_; lean_object* v_ty_2500_; lean_object* v___x_2501_; 
v_userName_2497_ = lean_ctor_get(v_decl_2496_, 2);
v_type_2498_ = lean_ctor_get(v_decl_2496_, 3);
v_bi_2499_ = lean_ctor_get_uint8(v_decl_2496_, sizeof(void*)*4);
v_ty_2500_ = lean_expr_abstract_range(v_type_2498_, v_n_2495_, v_xs_2489_);
lean_inc(v_userName_2497_);
v___x_2501_ = l_Lean_mkForall(v_userName_2497_, v_bi_2499_, v_ty_2500_, v_x_2491_);
v_x_2490_ = v_n_2495_;
v_x_2491_ = v___x_2501_;
goto _start;
}
else
{
lean_object* v_userName_2503_; lean_object* v_type_2504_; lean_object* v_value_2505_; uint8_t v_nondep_2506_; uint8_t v___x_2507_; 
v_userName_2503_ = lean_ctor_get(v_decl_2496_, 2);
v_type_2504_ = lean_ctor_get(v_decl_2496_, 3);
v_value_2505_ = lean_ctor_get(v_decl_2496_, 4);
v_nondep_2506_ = lean_ctor_get_uint8(v_decl_2496_, sizeof(void*)*5);
v___x_2507_ = lean_expr_has_loose_bvar(v_x_2491_, v_zero_2492_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_expr_lower_loose_bvars(v_x_2491_, v_one_2494_, v_one_2494_);
lean_dec_ref(v_x_2491_);
v_x_2490_ = v_n_2495_;
v_x_2491_ = v___x_2508_;
goto _start;
}
else
{
lean_object* v_ty_2510_; lean_object* v_val_2511_; lean_object* v___x_2512_; 
v_ty_2510_ = lean_expr_abstract_range(v_type_2504_, v_n_2495_, v_xs_2489_);
v_val_2511_ = lean_expr_abstract_range(v_value_2505_, v_n_2495_, v_xs_2489_);
lean_inc(v_userName_2503_);
v___x_2512_ = l_Lean_Expr_letE___override(v_userName_2503_, v_ty_2510_, v_val_2511_, v_x_2491_, v_nondep_2506_);
v_x_2490_ = v_n_2495_;
v_x_2491_ = v___x_2512_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0___boxed(lean_object* v_decls_2514_, lean_object* v_xs_2515_, lean_object* v_x_2516_, lean_object* v_x_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2514_, v_xs_2515_, v_x_2516_, v_x_2517_);
lean_dec_ref(v_xs_2515_);
lean_dec_ref(v_decls_2514_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(lean_object* v_decls_2519_, lean_object* v_xs_2520_, lean_object* v_x_2521_, lean_object* v_x_2522_){
_start:
{
lean_object* v_zero_2523_; uint8_t v_isZero_2524_; 
v_zero_2523_ = lean_unsigned_to_nat(0u);
v_isZero_2524_ = lean_nat_dec_eq(v_x_2521_, v_zero_2523_);
if (v_isZero_2524_ == 1)
{
return v_x_2522_;
}
else
{
lean_object* v_one_2525_; lean_object* v_n_2526_; lean_object* v_decl_2527_; 
v_one_2525_ = lean_unsigned_to_nat(1u);
v_n_2526_ = lean_nat_sub(v_x_2521_, v_one_2525_);
v_decl_2527_ = lean_array_fget_borrowed(v_decls_2519_, v_n_2526_);
if (lean_obj_tag(v_decl_2527_) == 0)
{
lean_object* v_userName_2528_; lean_object* v_type_2529_; uint8_t v_bi_2530_; lean_object* v_ty_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v_userName_2528_ = lean_ctor_get(v_decl_2527_, 2);
v_type_2529_ = lean_ctor_get(v_decl_2527_, 3);
v_bi_2530_ = lean_ctor_get_uint8(v_decl_2527_, sizeof(void*)*4);
v_ty_2531_ = lean_expr_abstract_range(v_type_2529_, v_n_2526_, v_xs_2520_);
lean_inc(v_userName_2528_);
v___x_2532_ = l_Lean_mkForall(v_userName_2528_, v_bi_2530_, v_ty_2531_, v_x_2522_);
v___x_2533_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2519_, v_xs_2520_, v_n_2526_, v___x_2532_);
return v___x_2533_;
}
else
{
lean_object* v_userName_2534_; lean_object* v_type_2535_; lean_object* v_value_2536_; uint8_t v_nondep_2537_; uint8_t v___x_2538_; 
v_userName_2534_ = lean_ctor_get(v_decl_2527_, 2);
v_type_2535_ = lean_ctor_get(v_decl_2527_, 3);
v_value_2536_ = lean_ctor_get(v_decl_2527_, 4);
v_nondep_2537_ = lean_ctor_get_uint8(v_decl_2527_, sizeof(void*)*5);
v___x_2538_ = lean_expr_has_loose_bvar(v_x_2522_, v_zero_2523_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_expr_lower_loose_bvars(v_x_2522_, v_one_2525_, v_one_2525_);
lean_dec_ref(v_x_2522_);
v___x_2540_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2519_, v_xs_2520_, v_n_2526_, v___x_2539_);
return v___x_2540_;
}
else
{
lean_object* v_ty_2541_; lean_object* v_val_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v_ty_2541_ = lean_expr_abstract_range(v_type_2535_, v_n_2526_, v_xs_2520_);
v_val_2542_ = lean_expr_abstract_range(v_value_2536_, v_n_2526_, v_xs_2520_);
lean_inc(v_userName_2534_);
v___x_2543_ = l_Lean_Expr_letE___override(v_userName_2534_, v_ty_2541_, v_val_2542_, v_x_2522_, v_nondep_2537_);
v___x_2544_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0_spec__0(v_decls_2519_, v_xs_2520_, v_n_2526_, v___x_2543_);
return v___x_2544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0___boxed(lean_object* v_decls_2545_, lean_object* v_xs_2546_, lean_object* v_x_2547_, lean_object* v_x_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2545_, v_xs_2546_, v_x_2547_, v_x_2548_);
lean_dec(v_x_2547_);
lean_dec_ref(v_xs_2546_);
lean_dec_ref(v_decls_2545_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall(lean_object* v_decls_2550_, lean_object* v_b_2551_){
_start:
{
size_t v_sz_2552_; size_t v___x_2553_; lean_object* v_xs_2554_; lean_object* v_b_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_sz_2552_ = lean_array_size(v_decls_2550_);
v___x_2553_ = ((size_t)0ULL);
lean_inc_ref(v_decls_2550_);
v_xs_2554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Closure_mkLambda_spec__0(v_sz_2552_, v___x_2553_, v_decls_2550_);
v_b_2555_ = lean_expr_abstract(v_b_2551_, v_xs_2554_);
v___x_2556_ = lean_array_get_size(v_decls_2550_);
v___x_2557_ = l_Nat_foldRev___at___00Lean_Meta_Closure_mkForall_spec__0(v_decls_2550_, v_xs_2554_, v___x_2556_, v_b_2555_);
lean_dec_ref(v_xs_2554_);
lean_dec_ref(v_decls_2550_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkForall___boxed(lean_object* v_decls_2558_, lean_object* v_b_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Meta_Closure_mkForall(v_decls_2558_, v_b_2559_);
lean_dec_ref(v_b_2559_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(lean_object* v_a_2561_, lean_object* v_cache_2562_, lean_object* v_a_x3f_2563_){
_start:
{
lean_object* v___x_2565_; lean_object* v_mctx_2566_; lean_object* v_zetaDeltaFVarIds_2567_; lean_object* v_postponed_2568_; lean_object* v_diag_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2579_; 
v___x_2565_ = lean_st_ref_take(v_a_2561_);
v_mctx_2566_ = lean_ctor_get(v___x_2565_, 0);
v_zetaDeltaFVarIds_2567_ = lean_ctor_get(v___x_2565_, 2);
v_postponed_2568_ = lean_ctor_get(v___x_2565_, 3);
v_diag_2569_ = lean_ctor_get(v___x_2565_, 4);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; 
v_unused_2580_ = lean_ctor_get(v___x_2565_, 1);
lean_dec(v_unused_2580_);
v___x_2571_ = v___x_2565_;
v_isShared_2572_ = v_isSharedCheck_2579_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_diag_2569_);
lean_inc(v_postponed_2568_);
lean_inc(v_zetaDeltaFVarIds_2567_);
lean_inc(v_mctx_2566_);
lean_dec(v___x_2565_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2579_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2573_ = lean_box(0);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v_cache_2562_);
v___x_2575_ = v___x_2571_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_mctx_2566_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_cache_2562_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_zetaDeltaFVarIds_2567_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_postponed_2568_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v_diag_2569_);
v___x_2575_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_st_ref_put(v_a_2561_, v___x_2575_);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2573_);
return v___x_2577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0___boxed(lean_object* v_a_2581_, lean_object* v_cache_2582_, lean_object* v_a_x3f_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2581_, v_cache_2582_, v_a_x3f_2583_);
lean_dec(v_a_x3f_2583_);
lean_dec(v_a_2581_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(lean_object* v_a_2586_, lean_object* v_zetaDeltaFVarIds_2587_, lean_object* v_a_x3f_2588_){
_start:
{
lean_object* v___x_2590_; lean_object* v_mctx_2591_; lean_object* v_cache_2592_; lean_object* v_postponed_2593_; lean_object* v_diag_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2604_; 
v___x_2590_ = lean_st_ref_take(v_a_2586_);
v_mctx_2591_ = lean_ctor_get(v___x_2590_, 0);
v_cache_2592_ = lean_ctor_get(v___x_2590_, 1);
v_postponed_2593_ = lean_ctor_get(v___x_2590_, 3);
v_diag_2594_ = lean_ctor_get(v___x_2590_, 4);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2604_ == 0)
{
lean_object* v_unused_2605_; 
v_unused_2605_ = lean_ctor_get(v___x_2590_, 2);
lean_dec(v_unused_2605_);
v___x_2596_ = v___x_2590_;
v_isShared_2597_ = v_isSharedCheck_2604_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_diag_2594_);
lean_inc(v_postponed_2593_);
lean_inc(v_cache_2592_);
lean_inc(v_mctx_2591_);
lean_dec(v___x_2590_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2604_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2598_ = lean_box(0);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 2, v_zetaDeltaFVarIds_2587_);
v___x_2600_ = v___x_2596_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_mctx_2591_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_cache_2592_);
lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_zetaDeltaFVarIds_2587_);
lean_ctor_set(v_reuseFailAlloc_2603_, 3, v_postponed_2593_);
lean_ctor_set(v_reuseFailAlloc_2603_, 4, v_diag_2594_);
v___x_2600_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = lean_st_ref_put(v_a_2586_, v___x_2600_);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2598_);
return v___x_2602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1___boxed(lean_object* v_a_2606_, lean_object* v_zetaDeltaFVarIds_2607_, lean_object* v_a_x3f_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2606_, v_zetaDeltaFVarIds_2607_, v_a_x3f_2608_);
lean_dec(v_a_x3f_2608_);
lean_dec(v_a_2606_);
return v_res_2610_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0(void){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__1);
v___x_2615_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
lean_ctor_set(v___x_2615_, 2, v___x_2614_);
lean_ctor_set(v___x_2615_, 3, v___x_2614_);
lean_ctor_set(v___x_2615_, 4, v___x_2614_);
lean_ctor_set(v___x_2615_, 5, v___x_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux(lean_object* v_type_2616_, lean_object* v_value_2617_, uint8_t v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v_cache_2627_; lean_object* v_a_2629_; lean_object* v___x_2640_; lean_object* v_mctx_2641_; lean_object* v_zetaDeltaFVarIds_2642_; lean_object* v_postponed_2643_; lean_object* v_diag_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2710_; 
v___x_2625_ = lean_box(1);
v___x_2626_ = lean_st_ref_get(v_a_2621_);
v_cache_2627_ = lean_ctor_get(v___x_2626_, 1);
lean_inc_ref(v_cache_2627_);
lean_dec(v___x_2626_);
v___x_2640_ = lean_st_ref_take(v_a_2621_);
v_mctx_2641_ = lean_ctor_get(v___x_2640_, 0);
v_zetaDeltaFVarIds_2642_ = lean_ctor_get(v___x_2640_, 2);
v_postponed_2643_ = lean_ctor_get(v___x_2640_, 3);
v_diag_2644_ = lean_ctor_get(v___x_2640_, 4);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; 
v_unused_2711_ = lean_ctor_get(v___x_2640_, 1);
lean_dec(v_unused_2711_);
v___x_2646_ = v___x_2640_;
v_isShared_2647_ = v_isSharedCheck_2710_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_diag_2644_);
lean_inc(v_postponed_2643_);
lean_inc(v_zetaDeltaFVarIds_2642_);
lean_inc(v_mctx_2641_);
lean_dec(v___x_2640_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2710_;
goto v_resetjp_2645_;
}
v___jp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
v___x_2630_ = lean_box(0);
v___x_2631_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2621_, v_cache_2627_, v___x_2630_);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; 
v_unused_2639_ = lean_ctor_get(v___x_2631_, 0);
lean_dec(v_unused_2639_);
v___x_2633_ = v___x_2631_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_dec(v___x_2631_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
lean_ctor_set_tag(v___x_2633_, 1);
lean_ctor_set(v___x_2633_, 0, v_a_2629_);
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2629_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2648_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__2);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 1, v___x_2648_);
v___x_2650_ = v___x_2646_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_mctx_2641_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_zetaDeltaFVarIds_2642_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_postponed_2643_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v_diag_2644_);
v___x_2650_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; lean_object* v_keyedConfig_2652_; lean_object* v_zetaDeltaSet_2653_; lean_object* v_lctx_2654_; lean_object* v_localInstances_2655_; lean_object* v_defEqCtx_x3f_2656_; lean_object* v_synthPendingDepth_2657_; lean_object* v_customCanUnfoldPredicate_x3f_2658_; uint8_t v_univApprox_2659_; uint8_t v_inTypeClassResolution_2660_; uint8_t v_cacheInferType_2661_; uint8_t v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v_mctx_2665_; lean_object* v_cache_2666_; lean_object* v_zetaDeltaFVarIds_2667_; lean_object* v_postponed_2668_; lean_object* v_diag_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2708_; 
v___x_2651_ = lean_st_ref_put(v_a_2621_, v___x_2650_);
v_keyedConfig_2652_ = lean_ctor_get(v_a_2620_, 0);
v_zetaDeltaSet_2653_ = lean_ctor_get(v_a_2620_, 1);
v_lctx_2654_ = lean_ctor_get(v_a_2620_, 2);
v_localInstances_2655_ = lean_ctor_get(v_a_2620_, 3);
v_defEqCtx_x3f_2656_ = lean_ctor_get(v_a_2620_, 4);
v_synthPendingDepth_2657_ = lean_ctor_get(v_a_2620_, 5);
v_customCanUnfoldPredicate_x3f_2658_ = lean_ctor_get(v_a_2620_, 6);
v_univApprox_2659_ = lean_ctor_get_uint8(v_a_2620_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2660_ = lean_ctor_get_uint8(v_a_2620_, sizeof(void*)*7 + 2);
v_cacheInferType_2661_ = lean_ctor_get_uint8(v_a_2620_, sizeof(void*)*7 + 3);
v___x_2662_ = 1;
lean_inc(v_customCanUnfoldPredicate_x3f_2658_);
lean_inc(v_synthPendingDepth_2657_);
lean_inc(v_defEqCtx_x3f_2656_);
lean_inc_ref(v_localInstances_2655_);
lean_inc_ref(v_lctx_2654_);
lean_inc(v_zetaDeltaSet_2653_);
lean_inc_ref(v_keyedConfig_2652_);
v___x_2663_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2663_, 0, v_keyedConfig_2652_);
lean_ctor_set(v___x_2663_, 1, v_zetaDeltaSet_2653_);
lean_ctor_set(v___x_2663_, 2, v_lctx_2654_);
lean_ctor_set(v___x_2663_, 3, v_localInstances_2655_);
lean_ctor_set(v___x_2663_, 4, v_defEqCtx_x3f_2656_);
lean_ctor_set(v___x_2663_, 5, v_synthPendingDepth_2657_);
lean_ctor_set(v___x_2663_, 6, v_customCanUnfoldPredicate_x3f_2658_);
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*7, v___x_2662_);
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*7 + 1, v_univApprox_2659_);
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2660_);
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*7 + 3, v_cacheInferType_2661_);
v___x_2664_ = lean_st_ref_take(v_a_2621_);
v_mctx_2665_ = lean_ctor_get(v___x_2664_, 0);
v_cache_2666_ = lean_ctor_get(v___x_2664_, 1);
v_zetaDeltaFVarIds_2667_ = lean_ctor_get(v___x_2664_, 2);
v_postponed_2668_ = lean_ctor_get(v___x_2664_, 3);
v_diag_2669_ = lean_ctor_get(v___x_2664_, 4);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2671_ = v___x_2664_;
v_isShared_2672_ = v_isSharedCheck_2708_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_diag_2669_);
lean_inc(v_postponed_2668_);
lean_inc(v_zetaDeltaFVarIds_2667_);
lean_inc(v_cache_2666_);
lean_inc(v_mctx_2665_);
lean_dec(v___x_2664_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2708_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v_a_2674_; lean_object* v___x_2678_; 
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 2, v___x_2625_);
v___x_2678_ = v___x_2671_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_mctx_2665_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_cache_2666_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v___x_2625_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_postponed_2668_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v_diag_2669_);
v___x_2678_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2677_;
}
v___jp_2673_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = lean_box(0);
v___x_2676_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2621_, v_zetaDeltaFVarIds_2667_, v___x_2675_);
lean_dec_ref(v___x_2676_);
v_a_2629_ = v_a_2674_;
goto v___jp_2628_;
}
v_reusejp_2677_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = lean_st_ref_put(v_a_2621_, v___x_2678_);
v___x_2680_ = l_Lean_Meta_Closure_collectExpr(v_type_2616_, v_a_2618_, v_a_2619_, v___x_2663_, v_a_2621_, v_a_2622_, v_a_2623_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2682_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = l_Lean_Meta_Closure_collectExpr(v_value_2617_, v_a_2618_, v_a_2619_, v___x_2663_, v_a_2621_, v_a_2622_, v_a_2623_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = l_Lean_Meta_Closure_process(v_a_2618_, v_a_2619_, v___x_2663_, v_a_2621_, v_a_2622_, v_a_2623_);
lean_dec_ref_known(v___x_2663_, 7);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2702_; 
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v___x_2684_, 0);
lean_dec(v_unused_2703_);
v___x_2686_ = v___x_2684_;
v_isShared_2687_ = v_isSharedCheck_2702_;
goto v_resetjp_2685_;
}
else
{
lean_dec(v___x_2684_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2702_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v_a_2681_);
lean_ctor_set(v___x_2688_, 1, v_a_2683_);
lean_inc_ref(v___x_2688_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set_tag(v___x_2686_, 1);
lean_ctor_set(v___x_2686_, 0, v___x_2688_);
v___x_2690_ = v___x_2686_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
v___x_2691_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__1(v_a_2621_, v_zetaDeltaFVarIds_2667_, v___x_2690_);
lean_dec_ref(v___x_2691_);
v___x_2692_ = l_Lean_Meta_Closure_mkValueTypeClosureAux___lam__0(v_a_2621_, v_cache_2627_, v___x_2690_);
lean_dec_ref(v___x_2690_);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v___x_2692_, 0);
lean_dec(v_unused_2700_);
v___x_2694_ = v___x_2692_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_dec(v___x_2692_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2688_);
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2688_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
else
{
lean_object* v_a_2704_; 
lean_dec(v_a_2683_);
lean_dec(v_a_2681_);
v_a_2704_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2684_, 1);
v_a_2674_ = v_a_2704_;
goto v___jp_2673_;
}
}
else
{
lean_object* v_a_2705_; 
lean_dec(v_a_2681_);
lean_dec_ref_known(v___x_2663_, 7);
v_a_2705_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2682_, 1);
v_a_2674_ = v_a_2705_;
goto v___jp_2673_;
}
}
else
{
lean_object* v_a_2706_; 
lean_dec_ref_known(v___x_2663_, 7);
lean_dec_ref(v_value_2617_);
v_a_2706_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2680_, 1);
v_a_2674_ = v_a_2706_;
goto v___jp_2673_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosureAux___boxed(lean_object* v_type_2712_, lean_object* v_value_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
uint8_t v_a_boxed_2721_; lean_object* v_res_2722_; 
v_a_boxed_2721_ = lean_unbox(v_a_2714_);
v_res_2722_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_2712_, v_value_2713_, v_a_boxed_2721_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
return v_res_2722_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_instMonadEIO___redArg();
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(lean_object* v_msg_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v_toApplicative_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2774_; 
v___x_2731_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__0);
v___x_2732_ = l_StateRefT_x27_instMonad___redArg(v___x_2731_);
v_toApplicative_2733_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2774_ == 0)
{
lean_object* v_unused_2775_; 
v_unused_2775_ = lean_ctor_get(v___x_2732_, 1);
lean_dec(v_unused_2775_);
v___x_2735_ = v___x_2732_;
v_isShared_2736_ = v_isSharedCheck_2774_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_toApplicative_2733_);
lean_dec(v___x_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2774_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v_toFunctor_2737_; lean_object* v_toSeq_2738_; lean_object* v_toSeqLeft_2739_; lean_object* v_toSeqRight_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2772_; 
v_toFunctor_2737_ = lean_ctor_get(v_toApplicative_2733_, 0);
v_toSeq_2738_ = lean_ctor_get(v_toApplicative_2733_, 2);
v_toSeqLeft_2739_ = lean_ctor_get(v_toApplicative_2733_, 3);
v_toSeqRight_2740_ = lean_ctor_get(v_toApplicative_2733_, 4);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_toApplicative_2733_);
if (v_isSharedCheck_2772_ == 0)
{
lean_object* v_unused_2773_; 
v_unused_2773_ = lean_ctor_get(v_toApplicative_2733_, 1);
lean_dec(v_unused_2773_);
v___x_2742_ = v_toApplicative_2733_;
v_isShared_2743_ = v_isSharedCheck_2772_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_toSeqRight_2740_);
lean_inc(v_toSeqLeft_2739_);
lean_inc(v_toSeq_2738_);
lean_inc(v_toFunctor_2737_);
lean_dec(v_toApplicative_2733_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2772_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___f_2744_; lean_object* v___f_2745_; lean_object* v___f_2746_; lean_object* v___f_2747_; lean_object* v___x_2748_; lean_object* v___f_2749_; lean_object* v___f_2750_; lean_object* v___f_2751_; lean_object* v___x_2753_; 
v___f_2744_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__1));
v___f_2745_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___closed__2));
lean_inc_ref(v_toFunctor_2737_);
v___f_2746_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2746_, 0, v_toFunctor_2737_);
v___f_2747_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2747_, 0, v_toFunctor_2737_);
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___f_2746_);
lean_ctor_set(v___x_2748_, 1, v___f_2747_);
v___f_2749_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2749_, 0, v_toSeqRight_2740_);
v___f_2750_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2750_, 0, v_toSeqLeft_2739_);
v___f_2751_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2751_, 0, v_toSeq_2738_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 4, v___f_2749_);
lean_ctor_set(v___x_2742_, 3, v___f_2750_);
lean_ctor_set(v___x_2742_, 2, v___f_2751_);
lean_ctor_set(v___x_2742_, 1, v___f_2744_);
lean_ctor_set(v___x_2742_, 0, v___x_2748_);
v___x_2753_ = v___x_2742_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2748_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v___f_2744_);
lean_ctor_set(v_reuseFailAlloc_2771_, 2, v___f_2751_);
lean_ctor_set(v_reuseFailAlloc_2771_, 3, v___f_2750_);
lean_ctor_set(v_reuseFailAlloc_2771_, 4, v___f_2749_);
v___x_2753_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2755_; 
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 1, v___f_2745_);
lean_ctor_set(v___x_2735_, 0, v___x_2753_);
v___x_2755_ = v___x_2735_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v___f_2745_);
v___x_2755_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___f_2756_; lean_object* v___f_2757_; lean_object* v___f_2758_; lean_object* v___f_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_12454__overap_2768_; lean_object* v___x_2769_; 
lean_inc_ref_n(v___x_2755_, 6);
v___f_2756_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2756_, 0, v___x_2755_);
v___f_2757_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2757_, 0, v___x_2755_);
v___f_2758_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2758_, 0, v___x_2755_);
v___f_2759_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2759_, 0, v___x_2755_);
v___x_2760_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2760_, 0, lean_box(0));
lean_closure_set(v___x_2760_, 1, lean_box(0));
lean_closure_set(v___x_2760_, 2, v___x_2755_);
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
lean_ctor_set(v___x_2761_, 1, v___f_2756_);
v___x_2762_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2762_, 0, lean_box(0));
lean_closure_set(v___x_2762_, 1, lean_box(0));
lean_closure_set(v___x_2762_, 2, v___x_2755_);
v___x_2763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
lean_ctor_set(v___x_2763_, 2, v___f_2757_);
lean_ctor_set(v___x_2763_, 3, v___f_2758_);
lean_ctor_set(v___x_2763_, 4, v___f_2759_);
v___x_2764_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2764_, 0, lean_box(0));
lean_closure_set(v___x_2764_, 1, lean_box(0));
lean_closure_set(v___x_2764_, 2, v___x_2755_);
v___x_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = lean_box(0);
v___x_2767_ = l_instInhabitedOfMonad___redArg(v___x_2765_, v___x_2766_);
v___x_12454__overap_2768_ = lean_panic_fn_borrowed(v___x_2767_, v_msg_2726_);
lean_dec(v___x_2767_);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
v___x_2769_ = lean_apply_4(v___x_12454__overap_2768_, v___y_2727_, v___y_2728_, v___y_2729_, lean_box(0));
return v___x_2769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4___boxed(lean_object* v_msg_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v_msg_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
return v_res_2781_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(lean_object* v_a_2782_, lean_object* v_x_2783_){
_start:
{
if (lean_obj_tag(v_x_2783_) == 0)
{
uint8_t v___x_2784_; 
v___x_2784_ = 0;
return v___x_2784_;
}
else
{
lean_object* v_key_2785_; lean_object* v_tail_2786_; uint8_t v___x_2787_; 
v_key_2785_ = lean_ctor_get(v_x_2783_, 0);
v_tail_2786_ = lean_ctor_get(v_x_2783_, 2);
v___x_2787_ = l_Lean_instBEqFVarId_beq(v_key_2785_, v_a_2782_);
if (v___x_2787_ == 0)
{
v_x_2783_ = v_tail_2786_;
goto _start;
}
else
{
return v___x_2787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg___boxed(lean_object* v_a_2789_, lean_object* v_x_2790_){
_start:
{
uint8_t v_res_2791_; lean_object* v_r_2792_; 
v_res_2791_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2789_, v_x_2790_);
lean_dec(v_x_2790_);
lean_dec(v_a_2789_);
v_r_2792_ = lean_box(v_res_2791_);
return v_r_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(lean_object* v_x_2793_, lean_object* v_x_2794_){
_start:
{
if (lean_obj_tag(v_x_2794_) == 0)
{
return v_x_2793_;
}
else
{
lean_object* v_key_2795_; lean_object* v_value_2796_; lean_object* v_tail_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2820_; 
v_key_2795_ = lean_ctor_get(v_x_2794_, 0);
v_value_2796_ = lean_ctor_get(v_x_2794_, 1);
v_tail_2797_ = lean_ctor_get(v_x_2794_, 2);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_x_2794_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2799_ = v_x_2794_;
v_isShared_2800_ = v_isSharedCheck_2820_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_tail_2797_);
lean_inc(v_value_2796_);
lean_inc(v_key_2795_);
lean_dec(v_x_2794_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2820_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; uint64_t v___x_2802_; uint64_t v___x_2803_; uint64_t v___x_2804_; uint64_t v_fold_2805_; uint64_t v___x_2806_; uint64_t v___x_2807_; uint64_t v___x_2808_; size_t v___x_2809_; size_t v___x_2810_; size_t v___x_2811_; size_t v___x_2812_; size_t v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2816_; 
v___x_2801_ = lean_array_get_size(v_x_2793_);
v___x_2802_ = l_Lean_instHashableFVarId_hash(v_key_2795_);
v___x_2803_ = 32ULL;
v___x_2804_ = lean_uint64_shift_right(v___x_2802_, v___x_2803_);
v_fold_2805_ = lean_uint64_xor(v___x_2802_, v___x_2804_);
v___x_2806_ = 16ULL;
v___x_2807_ = lean_uint64_shift_right(v_fold_2805_, v___x_2806_);
v___x_2808_ = lean_uint64_xor(v_fold_2805_, v___x_2807_);
v___x_2809_ = lean_uint64_to_usize(v___x_2808_);
v___x_2810_ = lean_usize_of_nat(v___x_2801_);
v___x_2811_ = ((size_t)1ULL);
v___x_2812_ = lean_usize_sub(v___x_2810_, v___x_2811_);
v___x_2813_ = lean_usize_land(v___x_2809_, v___x_2812_);
v___x_2814_ = lean_array_uget_borrowed(v_x_2793_, v___x_2813_);
lean_inc(v___x_2814_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 2, v___x_2814_);
v___x_2816_ = v___x_2799_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_key_2795_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_value_2796_);
lean_ctor_set(v_reuseFailAlloc_2819_, 2, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
lean_object* v___x_2817_; 
v___x_2817_ = lean_array_uset(v_x_2793_, v___x_2813_, v___x_2816_);
v_x_2793_ = v___x_2817_;
v_x_2794_ = v_tail_2797_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(lean_object* v_i_2821_, lean_object* v_source_2822_, lean_object* v_target_2823_){
_start:
{
lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2824_ = lean_array_get_size(v_source_2822_);
v___x_2825_ = lean_nat_dec_lt(v_i_2821_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_dec_ref(v_source_2822_);
lean_dec(v_i_2821_);
return v_target_2823_;
}
else
{
lean_object* v_es_2826_; lean_object* v___x_2827_; lean_object* v_source_2828_; lean_object* v_target_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_es_2826_ = lean_array_fget(v_source_2822_, v_i_2821_);
v___x_2827_ = lean_box(0);
v_source_2828_ = lean_array_fset(v_source_2822_, v_i_2821_, v___x_2827_);
v_target_2829_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_target_2823_, v_es_2826_);
v___x_2830_ = lean_unsigned_to_nat(1u);
v___x_2831_ = lean_nat_add(v_i_2821_, v___x_2830_);
lean_dec(v_i_2821_);
v_i_2821_ = v___x_2831_;
v_source_2822_ = v_source_2828_;
v_target_2823_ = v_target_2829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(lean_object* v_data_2833_){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v_nbuckets_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2834_ = lean_array_get_size(v_data_2833_);
v___x_2835_ = lean_unsigned_to_nat(2u);
v_nbuckets_2836_ = lean_nat_mul(v___x_2834_, v___x_2835_);
v___x_2837_ = lean_unsigned_to_nat(0u);
v___x_2838_ = lean_box(0);
v___x_2839_ = lean_mk_array(v_nbuckets_2836_, v___x_2838_);
v___x_2840_ = lean_array_propagate_mark(v_data_2833_, v___x_2839_);
v___x_2841_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v___x_2837_, v_data_2833_, v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(lean_object* v_m_2842_, lean_object* v_a_2843_, lean_object* v_b_2844_){
_start:
{
lean_object* v_size_2845_; lean_object* v_buckets_2846_; lean_object* v___x_2847_; uint64_t v___x_2848_; uint64_t v___x_2849_; uint64_t v___x_2850_; uint64_t v_fold_2851_; uint64_t v___x_2852_; uint64_t v___x_2853_; uint64_t v___x_2854_; size_t v___x_2855_; size_t v___x_2856_; size_t v___x_2857_; size_t v___x_2858_; size_t v___x_2859_; lean_object* v_bkt_2860_; uint8_t v___x_2861_; 
v_size_2845_ = lean_ctor_get(v_m_2842_, 0);
v_buckets_2846_ = lean_ctor_get(v_m_2842_, 1);
v___x_2847_ = lean_array_get_size(v_buckets_2846_);
v___x_2848_ = l_Lean_instHashableFVarId_hash(v_a_2843_);
v___x_2849_ = 32ULL;
v___x_2850_ = lean_uint64_shift_right(v___x_2848_, v___x_2849_);
v_fold_2851_ = lean_uint64_xor(v___x_2848_, v___x_2850_);
v___x_2852_ = 16ULL;
v___x_2853_ = lean_uint64_shift_right(v_fold_2851_, v___x_2852_);
v___x_2854_ = lean_uint64_xor(v_fold_2851_, v___x_2853_);
v___x_2855_ = lean_uint64_to_usize(v___x_2854_);
v___x_2856_ = lean_usize_of_nat(v___x_2847_);
v___x_2857_ = ((size_t)1ULL);
v___x_2858_ = lean_usize_sub(v___x_2856_, v___x_2857_);
v___x_2859_ = lean_usize_land(v___x_2855_, v___x_2858_);
v_bkt_2860_ = lean_array_uget_borrowed(v_buckets_2846_, v___x_2859_);
v___x_2861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2843_, v_bkt_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2882_; 
lean_inc_ref(v_buckets_2846_);
lean_inc(v_size_2845_);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_m_2842_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; lean_object* v_unused_2884_; 
v_unused_2883_ = lean_ctor_get(v_m_2842_, 1);
lean_dec(v_unused_2883_);
v_unused_2884_ = lean_ctor_get(v_m_2842_, 0);
lean_dec(v_unused_2884_);
v___x_2863_ = v_m_2842_;
v_isShared_2864_ = v_isSharedCheck_2882_;
goto v_resetjp_2862_;
}
else
{
lean_dec(v_m_2842_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2882_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; lean_object* v_size_x27_2866_; lean_object* v___x_2867_; lean_object* v_buckets_x27_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v___x_2865_ = lean_unsigned_to_nat(1u);
v_size_x27_2866_ = lean_nat_add(v_size_2845_, v___x_2865_);
lean_dec(v_size_2845_);
lean_inc(v_bkt_2860_);
v___x_2867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2867_, 0, v_a_2843_);
lean_ctor_set(v___x_2867_, 1, v_b_2844_);
lean_ctor_set(v___x_2867_, 2, v_bkt_2860_);
v_buckets_x27_2868_ = lean_array_uset(v_buckets_2846_, v___x_2859_, v___x_2867_);
v___x_2869_ = lean_unsigned_to_nat(4u);
v___x_2870_ = lean_nat_mul(v_size_x27_2866_, v___x_2869_);
v___x_2871_ = lean_unsigned_to_nat(3u);
v___x_2872_ = lean_nat_div(v___x_2870_, v___x_2871_);
lean_dec(v___x_2870_);
v___x_2873_ = lean_array_get_size(v_buckets_x27_2868_);
v___x_2874_ = lean_nat_dec_le(v___x_2872_, v___x_2873_);
lean_dec(v___x_2872_);
if (v___x_2874_ == 0)
{
lean_object* v_val_2875_; lean_object* v___x_2877_; 
v_val_2875_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_2868_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v_val_2875_);
lean_ctor_set(v___x_2863_, 0, v_size_x27_2866_);
v___x_2877_ = v___x_2863_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_size_x27_2866_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_val_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
else
{
lean_object* v___x_2880_; 
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v_buckets_x27_2868_);
lean_ctor_set(v___x_2863_, 0, v_size_x27_2866_);
v___x_2880_ = v___x_2863_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_size_x27_2866_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_buckets_x27_2868_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
else
{
lean_dec(v_b_2844_);
lean_dec(v_a_2843_);
return v_m_2842_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(lean_object* v_m_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_buckets_2887_; lean_object* v___x_2888_; uint64_t v___x_2889_; uint64_t v___x_2890_; uint64_t v___x_2891_; uint64_t v_fold_2892_; uint64_t v___x_2893_; uint64_t v___x_2894_; uint64_t v___x_2895_; size_t v___x_2896_; size_t v___x_2897_; size_t v___x_2898_; size_t v___x_2899_; size_t v___x_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
v_buckets_2887_ = lean_ctor_get(v_m_2885_, 1);
v___x_2888_ = lean_array_get_size(v_buckets_2887_);
v___x_2889_ = l_Lean_instHashableFVarId_hash(v_a_2886_);
v___x_2890_ = 32ULL;
v___x_2891_ = lean_uint64_shift_right(v___x_2889_, v___x_2890_);
v_fold_2892_ = lean_uint64_xor(v___x_2889_, v___x_2891_);
v___x_2893_ = 16ULL;
v___x_2894_ = lean_uint64_shift_right(v_fold_2892_, v___x_2893_);
v___x_2895_ = lean_uint64_xor(v_fold_2892_, v___x_2894_);
v___x_2896_ = lean_uint64_to_usize(v___x_2895_);
v___x_2897_ = lean_usize_of_nat(v___x_2888_);
v___x_2898_ = ((size_t)1ULL);
v___x_2899_ = lean_usize_sub(v___x_2897_, v___x_2898_);
v___x_2900_ = lean_usize_land(v___x_2896_, v___x_2899_);
v___x_2901_ = lean_array_uget_borrowed(v_buckets_2887_, v___x_2900_);
v___x_2902_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_2886_, v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg___boxed(lean_object* v_m_2903_, lean_object* v_a_2904_){
_start:
{
uint8_t v_res_2905_; lean_object* v_r_2906_; 
v_res_2905_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_2903_, v_a_2904_);
lean_dec(v_a_2904_);
lean_dec_ref(v_m_2903_);
v_r_2906_ = lean_box(v_res_2905_);
return v_r_2906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(lean_object* v_a_2907_, lean_object* v_x_2908_){
_start:
{
if (lean_obj_tag(v_x_2908_) == 0)
{
lean_object* v___x_2909_; 
v___x_2909_ = lean_box(0);
return v___x_2909_;
}
else
{
lean_object* v_key_2910_; lean_object* v_value_2911_; lean_object* v_tail_2912_; uint8_t v___x_2913_; 
v_key_2910_ = lean_ctor_get(v_x_2908_, 0);
v_value_2911_ = lean_ctor_get(v_x_2908_, 1);
v_tail_2912_ = lean_ctor_get(v_x_2908_, 2);
v___x_2913_ = lean_expr_eqv(v_key_2910_, v_a_2907_);
if (v___x_2913_ == 0)
{
v_x_2908_ = v_tail_2912_;
goto _start;
}
else
{
lean_object* v___x_2915_; 
lean_inc(v_value_2911_);
v___x_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2915_, 0, v_value_2911_);
return v___x_2915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_a_2916_, lean_object* v_x_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2916_, v_x_2917_);
lean_dec(v_x_2917_);
lean_dec_ref(v_a_2916_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(lean_object* v_m_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_buckets_2921_; lean_object* v___x_2922_; uint64_t v___x_2923_; uint64_t v___x_2924_; uint64_t v___x_2925_; uint64_t v_fold_2926_; uint64_t v___x_2927_; uint64_t v___x_2928_; uint64_t v___x_2929_; size_t v___x_2930_; size_t v___x_2931_; size_t v___x_2932_; size_t v___x_2933_; size_t v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_buckets_2921_ = lean_ctor_get(v_m_2919_, 1);
v___x_2922_ = lean_array_get_size(v_buckets_2921_);
v___x_2923_ = l_Lean_Expr_hash(v_a_2920_);
v___x_2924_ = 32ULL;
v___x_2925_ = lean_uint64_shift_right(v___x_2923_, v___x_2924_);
v_fold_2926_ = lean_uint64_xor(v___x_2923_, v___x_2925_);
v___x_2927_ = 16ULL;
v___x_2928_ = lean_uint64_shift_right(v_fold_2926_, v___x_2927_);
v___x_2929_ = lean_uint64_xor(v_fold_2926_, v___x_2928_);
v___x_2930_ = lean_uint64_to_usize(v___x_2929_);
v___x_2931_ = lean_usize_of_nat(v___x_2922_);
v___x_2932_ = ((size_t)1ULL);
v___x_2933_ = lean_usize_sub(v___x_2931_, v___x_2932_);
v___x_2934_ = lean_usize_land(v___x_2930_, v___x_2933_);
v___x_2935_ = lean_array_uget_borrowed(v_buckets_2921_, v___x_2934_);
v___x_2936_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_2920_, v___x_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg___boxed(lean_object* v_m_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_2937_, v_a_2938_);
lean_dec_ref(v_a_2938_);
lean_dec_ref(v_m_2937_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(lean_object* v_a_2940_, lean_object* v_b_2941_, lean_object* v_x_2942_){
_start:
{
if (lean_obj_tag(v_x_2942_) == 0)
{
lean_dec(v_b_2941_);
lean_dec_ref(v_a_2940_);
return v_x_2942_;
}
else
{
lean_object* v_key_2943_; lean_object* v_value_2944_; lean_object* v_tail_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2957_; 
v_key_2943_ = lean_ctor_get(v_x_2942_, 0);
v_value_2944_ = lean_ctor_get(v_x_2942_, 1);
v_tail_2945_ = lean_ctor_get(v_x_2942_, 2);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_x_2942_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2947_ = v_x_2942_;
v_isShared_2948_ = v_isSharedCheck_2957_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_tail_2945_);
lean_inc(v_value_2944_);
lean_inc(v_key_2943_);
lean_dec(v_x_2942_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2957_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
uint8_t v___x_2949_; 
v___x_2949_ = lean_expr_eqv(v_key_2943_, v_a_2940_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_2940_, v_b_2941_, v_tail_2945_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 2, v___x_2950_);
v___x_2952_ = v___x_2947_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_key_2943_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_value_2944_);
lean_ctor_set(v_reuseFailAlloc_2953_, 2, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
else
{
lean_object* v___x_2955_; 
lean_dec(v_value_2944_);
lean_dec(v_key_2943_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v_b_2941_);
lean_ctor_set(v___x_2947_, 0, v_a_2940_);
v___x_2955_ = v___x_2947_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2940_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_b_2941_);
lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_tail_2945_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(lean_object* v_x_2958_, lean_object* v_x_2959_){
_start:
{
if (lean_obj_tag(v_x_2959_) == 0)
{
return v_x_2958_;
}
else
{
lean_object* v_key_2960_; lean_object* v_value_2961_; lean_object* v_tail_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2985_; 
v_key_2960_ = lean_ctor_get(v_x_2959_, 0);
v_value_2961_ = lean_ctor_get(v_x_2959_, 1);
v_tail_2962_ = lean_ctor_get(v_x_2959_, 2);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_x_2959_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2964_ = v_x_2959_;
v_isShared_2965_ = v_isSharedCheck_2985_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_tail_2962_);
lean_inc(v_value_2961_);
lean_inc(v_key_2960_);
lean_dec(v_x_2959_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2985_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2966_; uint64_t v___x_2967_; uint64_t v___x_2968_; uint64_t v___x_2969_; uint64_t v_fold_2970_; uint64_t v___x_2971_; uint64_t v___x_2972_; uint64_t v___x_2973_; size_t v___x_2974_; size_t v___x_2975_; size_t v___x_2976_; size_t v___x_2977_; size_t v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2981_; 
v___x_2966_ = lean_array_get_size(v_x_2958_);
v___x_2967_ = l_Lean_Expr_hash(v_key_2960_);
v___x_2968_ = 32ULL;
v___x_2969_ = lean_uint64_shift_right(v___x_2967_, v___x_2968_);
v_fold_2970_ = lean_uint64_xor(v___x_2967_, v___x_2969_);
v___x_2971_ = 16ULL;
v___x_2972_ = lean_uint64_shift_right(v_fold_2970_, v___x_2971_);
v___x_2973_ = lean_uint64_xor(v_fold_2970_, v___x_2972_);
v___x_2974_ = lean_uint64_to_usize(v___x_2973_);
v___x_2975_ = lean_usize_of_nat(v___x_2966_);
v___x_2976_ = ((size_t)1ULL);
v___x_2977_ = lean_usize_sub(v___x_2975_, v___x_2976_);
v___x_2978_ = lean_usize_land(v___x_2974_, v___x_2977_);
v___x_2979_ = lean_array_uget_borrowed(v_x_2958_, v___x_2978_);
lean_inc(v___x_2979_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 2, v___x_2979_);
v___x_2981_ = v___x_2964_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_key_2960_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_value_2961_);
lean_ctor_set(v_reuseFailAlloc_2984_, 2, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2982_; 
v___x_2982_ = lean_array_uset(v_x_2958_, v___x_2978_, v___x_2981_);
v_x_2958_ = v___x_2982_;
v_x_2959_ = v_tail_2962_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(lean_object* v_i_2986_, lean_object* v_source_2987_, lean_object* v_target_2988_){
_start:
{
lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2989_ = lean_array_get_size(v_source_2987_);
v___x_2990_ = lean_nat_dec_lt(v_i_2986_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_dec_ref(v_source_2987_);
lean_dec(v_i_2986_);
return v_target_2988_;
}
else
{
lean_object* v_es_2991_; lean_object* v___x_2992_; lean_object* v_source_2993_; lean_object* v_target_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v_es_2991_ = lean_array_fget(v_source_2987_, v_i_2986_);
v___x_2992_ = lean_box(0);
v_source_2993_ = lean_array_fset(v_source_2987_, v_i_2986_, v___x_2992_);
v_target_2994_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_target_2988_, v_es_2991_);
v___x_2995_ = lean_unsigned_to_nat(1u);
v___x_2996_ = lean_nat_add(v_i_2986_, v___x_2995_);
lean_dec(v_i_2986_);
v_i_2986_ = v___x_2996_;
v_source_2987_ = v_source_2993_;
v_target_2988_ = v_target_2994_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(lean_object* v_data_2998_){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v_nbuckets_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_2999_ = lean_array_get_size(v_data_2998_);
v___x_3000_ = lean_unsigned_to_nat(2u);
v_nbuckets_3001_ = lean_nat_mul(v___x_2999_, v___x_3000_);
v___x_3002_ = lean_unsigned_to_nat(0u);
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_mk_array(v_nbuckets_3001_, v___x_3003_);
v___x_3005_ = lean_array_propagate_mark(v_data_2998_, v___x_3004_);
v___x_3006_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v___x_3002_, v_data_2998_, v___x_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(lean_object* v_a_3007_, lean_object* v_x_3008_){
_start:
{
if (lean_obj_tag(v_x_3008_) == 0)
{
uint8_t v___x_3009_; 
v___x_3009_ = 0;
return v___x_3009_;
}
else
{
lean_object* v_key_3010_; lean_object* v_tail_3011_; uint8_t v___x_3012_; 
v_key_3010_ = lean_ctor_get(v_x_3008_, 0);
v_tail_3011_ = lean_ctor_get(v_x_3008_, 2);
v___x_3012_ = lean_expr_eqv(v_key_3010_, v_a_3007_);
if (v___x_3012_ == 0)
{
v_x_3008_ = v_tail_3011_;
goto _start;
}
else
{
return v___x_3012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_3014_, lean_object* v_x_3015_){
_start:
{
uint8_t v_res_3016_; lean_object* v_r_3017_; 
v_res_3016_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3014_, v_x_3015_);
lean_dec(v_x_3015_);
lean_dec_ref(v_a_3014_);
v_r_3017_ = lean_box(v_res_3016_);
return v_r_3017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(lean_object* v_m_3018_, lean_object* v_a_3019_, lean_object* v_b_3020_){
_start:
{
lean_object* v_size_3021_; lean_object* v_buckets_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3065_; 
v_size_3021_ = lean_ctor_get(v_m_3018_, 0);
v_buckets_3022_ = lean_ctor_get(v_m_3018_, 1);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_m_3018_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3024_ = v_m_3018_;
v_isShared_3025_ = v_isSharedCheck_3065_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_buckets_3022_);
lean_inc(v_size_3021_);
lean_dec(v_m_3018_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3065_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3026_; uint64_t v___x_3027_; uint64_t v___x_3028_; uint64_t v___x_3029_; uint64_t v_fold_3030_; uint64_t v___x_3031_; uint64_t v___x_3032_; uint64_t v___x_3033_; size_t v___x_3034_; size_t v___x_3035_; size_t v___x_3036_; size_t v___x_3037_; size_t v___x_3038_; lean_object* v_bkt_3039_; uint8_t v___x_3040_; 
v___x_3026_ = lean_array_get_size(v_buckets_3022_);
v___x_3027_ = l_Lean_Expr_hash(v_a_3019_);
v___x_3028_ = 32ULL;
v___x_3029_ = lean_uint64_shift_right(v___x_3027_, v___x_3028_);
v_fold_3030_ = lean_uint64_xor(v___x_3027_, v___x_3029_);
v___x_3031_ = 16ULL;
v___x_3032_ = lean_uint64_shift_right(v_fold_3030_, v___x_3031_);
v___x_3033_ = lean_uint64_xor(v_fold_3030_, v___x_3032_);
v___x_3034_ = lean_uint64_to_usize(v___x_3033_);
v___x_3035_ = lean_usize_of_nat(v___x_3026_);
v___x_3036_ = ((size_t)1ULL);
v___x_3037_ = lean_usize_sub(v___x_3035_, v___x_3036_);
v___x_3038_ = lean_usize_land(v___x_3034_, v___x_3037_);
v_bkt_3039_ = lean_array_uget_borrowed(v_buckets_3022_, v___x_3038_);
v___x_3040_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3019_, v_bkt_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; lean_object* v_size_x27_3042_; lean_object* v___x_3043_; lean_object* v_buckets_x27_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3041_ = lean_unsigned_to_nat(1u);
v_size_x27_3042_ = lean_nat_add(v_size_3021_, v___x_3041_);
lean_dec(v_size_3021_);
lean_inc(v_bkt_3039_);
v___x_3043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3043_, 0, v_a_3019_);
lean_ctor_set(v___x_3043_, 1, v_b_3020_);
lean_ctor_set(v___x_3043_, 2, v_bkt_3039_);
v_buckets_x27_3044_ = lean_array_uset(v_buckets_3022_, v___x_3038_, v___x_3043_);
v___x_3045_ = lean_unsigned_to_nat(4u);
v___x_3046_ = lean_nat_mul(v_size_x27_3042_, v___x_3045_);
v___x_3047_ = lean_unsigned_to_nat(3u);
v___x_3048_ = lean_nat_div(v___x_3046_, v___x_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_array_get_size(v_buckets_x27_3044_);
v___x_3050_ = lean_nat_dec_le(v___x_3048_, v___x_3049_);
lean_dec(v___x_3048_);
if (v___x_3050_ == 0)
{
lean_object* v_val_3051_; lean_object* v___x_3053_; 
v_val_3051_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_buckets_x27_3044_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 1, v_val_3051_);
lean_ctor_set(v___x_3024_, 0, v_size_x27_3042_);
v___x_3053_ = v___x_3024_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_size_x27_3042_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_val_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
else
{
lean_object* v___x_3056_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 1, v_buckets_x27_3044_);
lean_ctor_set(v___x_3024_, 0, v_size_x27_3042_);
v___x_3056_ = v___x_3024_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_size_x27_3042_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v_buckets_x27_3044_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
else
{
lean_object* v___x_3058_; lean_object* v_buckets_x27_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
lean_inc(v_bkt_3039_);
v___x_3058_ = lean_box(0);
v_buckets_x27_3059_ = lean_array_uset(v_buckets_3022_, v___x_3038_, v___x_3058_);
v___x_3060_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3019_, v_b_3020_, v_bkt_3039_);
v___x_3061_ = lean_array_uset(v_buckets_x27_3059_, v___x_3038_, v___x_3060_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 1, v___x_3061_);
v___x_3063_ = v___x_3024_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_size_3021_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(lean_object* v_g_3066_, lean_object* v_e_3067_, lean_object* v_a_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_a_3074_; lean_object* v_fst_3075_; lean_object* v___y_3081_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_st_ref_get(v_a_3068_);
v___x_3085_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v___x_3084_, v_e_3067_);
lean_dec(v___x_3084_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v___x_3086_; 
lean_inc_ref(v_g_3066_);
lean_inc(v___y_3071_);
lean_inc_ref(v___y_3070_);
lean_inc_ref(v_e_3067_);
v___x_3086_ = lean_apply_5(v_g_3066_, v_e_3067_, v___y_3069_, v___y_3070_, v___y_3071_, lean_box(0));
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v_fst_3088_; lean_object* v_snd_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3134_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3086_, 1);
v_fst_3088_ = lean_ctor_get(v_a_3087_, 0);
v_snd_3089_ = lean_ctor_get(v_a_3087_, 1);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_a_3087_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3091_ = v_a_3087_;
v_isShared_3092_ = v_isSharedCheck_3134_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_snd_3089_);
lean_inc(v_fst_3088_);
lean_dec(v_a_3087_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3134_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v_d_3094_; lean_object* v_b_3095_; lean_object* v___y_3096_; uint8_t v___x_3101_; 
v___x_3101_ = lean_unbox(v_fst_3088_);
lean_dec(v_fst_3088_);
if (v___x_3101_ == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
lean_dec_ref(v_g_3066_);
v___x_3102_ = lean_box(0);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3102_);
v___x_3104_ = v___x_3091_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_snd_3089_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
v_a_3074_ = v___x_3104_;
v_fst_3075_ = v___x_3102_;
goto v___jp_3073_;
}
}
else
{
switch(lean_obj_tag(v_e_3067_))
{
case 7:
{
lean_object* v_binderType_3106_; lean_object* v_body_3107_; 
lean_del_object(v___x_3091_);
v_binderType_3106_ = lean_ctor_get(v_e_3067_, 1);
v_body_3107_ = lean_ctor_get(v_e_3067_, 2);
lean_inc_ref(v_body_3107_);
lean_inc_ref(v_binderType_3106_);
v_d_3094_ = v_binderType_3106_;
v_b_3095_ = v_body_3107_;
v___y_3096_ = v_a_3068_;
goto v___jp_3093_;
}
case 6:
{
lean_object* v_binderType_3108_; lean_object* v_body_3109_; 
lean_del_object(v___x_3091_);
v_binderType_3108_ = lean_ctor_get(v_e_3067_, 1);
v_body_3109_ = lean_ctor_get(v_e_3067_, 2);
lean_inc_ref(v_body_3109_);
lean_inc_ref(v_binderType_3108_);
v_d_3094_ = v_binderType_3108_;
v_b_3095_ = v_body_3109_;
v___y_3096_ = v_a_3068_;
goto v___jp_3093_;
}
case 8:
{
lean_object* v_type_3110_; lean_object* v_value_3111_; lean_object* v_body_3112_; lean_object* v___x_3113_; 
lean_del_object(v___x_3091_);
v_type_3110_ = lean_ctor_get(v_e_3067_, 1);
v_value_3111_ = lean_ctor_get(v_e_3067_, 2);
v_body_3112_ = lean_ctor_get(v_e_3067_, 3);
lean_inc_ref(v_type_3110_);
lean_inc_ref(v_g_3066_);
v___x_3113_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3066_, v_type_3110_, v_a_3068_, v_snd_3089_, v___y_3070_, v___y_3071_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v_snd_3115_; lean_object* v___x_3116_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
v_snd_3115_ = lean_ctor_get(v_a_3114_, 1);
lean_inc(v_snd_3115_);
lean_dec(v_a_3114_);
lean_inc_ref(v_value_3111_);
lean_inc_ref(v_g_3066_);
v___x_3116_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3066_, v_value_3111_, v_a_3068_, v_snd_3115_, v___y_3070_, v___y_3071_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v_snd_3118_; lean_object* v___x_3119_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v_snd_3118_ = lean_ctor_get(v_a_3117_, 1);
lean_inc(v_snd_3118_);
lean_dec(v_a_3117_);
lean_inc_ref(v_body_3112_);
v___x_3119_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3066_, v_body_3112_, v_a_3068_, v_snd_3118_, v___y_3070_, v___y_3071_);
v___y_3081_ = v___x_3119_;
goto v___jp_3080_;
}
else
{
lean_dec_ref(v_g_3066_);
v___y_3081_ = v___x_3116_;
goto v___jp_3080_;
}
}
else
{
lean_dec_ref(v_g_3066_);
v___y_3081_ = v___x_3113_;
goto v___jp_3080_;
}
}
case 5:
{
lean_object* v_fn_3120_; lean_object* v_arg_3121_; lean_object* v___x_3122_; 
lean_del_object(v___x_3091_);
v_fn_3120_ = lean_ctor_get(v_e_3067_, 0);
v_arg_3121_ = lean_ctor_get(v_e_3067_, 1);
lean_inc_ref(v_fn_3120_);
lean_inc_ref(v_g_3066_);
v___x_3122_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3066_, v_fn_3120_, v_a_3068_, v_snd_3089_, v___y_3070_, v___y_3071_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v_snd_3124_; lean_object* v___x_3125_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___x_3122_, 1);
v_snd_3124_ = lean_ctor_get(v_a_3123_, 1);
lean_inc(v_snd_3124_);
lean_dec(v_a_3123_);
lean_inc_ref(v_arg_3121_);
v___x_3125_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3066_, v_arg_3121_, v_a_3068_, v_snd_3124_, v___y_3070_, v___y_3071_);
v___y_3081_ = v___x_3125_;
goto v___jp_3080_;
}
else
{
lean_dec_ref(v_g_3066_);
v___y_3081_ = v___x_3122_;
goto v___jp_3080_;
}
}
case 10:
{
lean_object* v_expr_3126_; lean_object* v___x_3127_; 
lean_del_object(v___x_3091_);
v_expr_3126_ = lean_ctor_get(v_e_3067_, 1);
lean_inc_ref(v_expr_3126_);
v___x_3127_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3066_, v_expr_3126_, v_a_3068_, v_snd_3089_, v___y_3070_, v___y_3071_);
v___y_3081_ = v___x_3127_;
goto v___jp_3080_;
}
case 11:
{
lean_object* v_struct_3128_; lean_object* v___x_3129_; 
lean_del_object(v___x_3091_);
v_struct_3128_ = lean_ctor_get(v_e_3067_, 2);
lean_inc_ref(v_struct_3128_);
v___x_3129_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3066_, v_struct_3128_, v_a_3068_, v_snd_3089_, v___y_3070_, v___y_3071_);
v___y_3081_ = v___x_3129_;
goto v___jp_3080_;
}
default: 
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
lean_dec_ref(v_g_3066_);
v___x_3130_ = lean_box(0);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3130_);
v___x_3132_ = v___x_3091_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v_snd_3089_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
v_a_3074_ = v___x_3132_;
v_fst_3075_ = v___x_3130_;
goto v___jp_3073_;
}
}
}
}
v___jp_3093_:
{
lean_object* v___x_3097_; 
lean_inc_ref(v_g_3066_);
v___x_3097_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3066_, v_d_3094_, v___y_3096_, v_snd_3089_, v___y_3070_, v___y_3071_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v_snd_3099_; lean_object* v___x_3100_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v_snd_3099_ = lean_ctor_get(v_a_3098_, 1);
lean_inc(v_snd_3099_);
lean_dec(v_a_3098_);
v___x_3100_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3066_, v_b_3095_, v___y_3096_, v_snd_3099_, v___y_3070_, v___y_3071_);
v___y_3081_ = v___x_3100_;
goto v___jp_3080_;
}
else
{
lean_dec_ref(v_b_3095_);
lean_dec_ref(v_g_3066_);
v___y_3081_ = v___x_3097_;
goto v___jp_3080_;
}
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec_ref(v_e_3067_);
lean_dec_ref(v_g_3066_);
v_a_3135_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3086_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3086_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
else
{
lean_object* v_val_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3151_; 
lean_dec_ref(v_e_3067_);
lean_dec_ref(v_g_3066_);
v_val_3143_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3145_ = v___x_3085_;
v_isShared_3146_ = v_isSharedCheck_3151_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_val_3143_);
lean_dec(v___x_3085_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3151_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_val_3143_);
lean_ctor_set(v___x_3147_, 1, v___y_3069_);
if (v_isShared_3146_ == 0)
{
lean_ctor_set_tag(v___x_3145_, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3147_);
v___x_3149_ = v___x_3145_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
v___jp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3076_ = lean_st_ref_take(v_a_3068_);
v___x_3077_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v___x_3076_, v_e_3067_, v_fst_3075_);
v___x_3078_ = lean_st_ref_put(v_a_3068_, v___x_3077_);
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v_a_3074_);
return v___x_3079_;
}
v___jp_3080_:
{
if (lean_obj_tag(v___y_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v_fst_3083_; 
v_a_3082_ = lean_ctor_get(v___y_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___y_3081_, 1);
v_fst_3083_ = lean_ctor_get(v_a_3082_, 0);
lean_inc(v_fst_3083_);
v_a_3074_ = v_a_3082_;
v_fst_3075_ = v_fst_3083_;
goto v___jp_3073_;
}
else
{
lean_dec_ref(v_e_3067_);
return v___y_3081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3___boxed(lean_object* v_g_3152_, lean_object* v_e_3153_, lean_object* v_a_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v_g_3152_, v_e_3153_, v_a_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v_a_3154_);
return v_res_3159_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosureAux___closed__0);
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
return v___x_3161_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3163_ = lean_unsigned_to_nat(0u);
v___x_3164_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
lean_ctor_set(v___x_3164_, 2, v___x_3163_);
lean_ctor_set(v___x_3164_, 3, v___x_3163_);
lean_ctor_set(v___x_3164_, 4, v___x_3162_);
lean_ctor_set(v___x_3164_, 5, v___x_3162_);
lean_ctor_set(v___x_3164_, 6, v___x_3162_);
lean_ctor_set(v___x_3164_, 7, v___x_3162_);
lean_ctor_set(v___x_3164_, 8, v___x_3162_);
lean_ctor_set(v___x_3164_, 9, v___x_3162_);
lean_ctor_set(v___x_3164_, 10, v___x_3162_);
return v___x_3164_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = lean_unsigned_to_nat(32u);
v___x_3166_ = lean_mk_empty_array_with_capacity(v___x_3165_);
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3(void){
_start:
{
size_t v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3168_ = ((size_t)5ULL);
v___x_3169_ = lean_unsigned_to_nat(0u);
v___x_3170_ = lean_unsigned_to_nat(32u);
v___x_3171_ = lean_mk_empty_array_with_capacity(v___x_3170_);
v___x_3172_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__2);
v___x_3173_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v___x_3171_);
lean_ctor_set(v___x_3173_, 2, v___x_3169_);
lean_ctor_set(v___x_3173_, 3, v___x_3169_);
lean_ctor_set_usize(v___x_3173_, 4, v___x_3168_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3174_ = lean_box(1);
v___x_3175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__3);
v___x_3176_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__0);
v___x_3177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v___x_3175_);
lean_ctor_set(v___x_3177_, 2, v___x_3174_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(lean_object* v_msgData_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v___x_3182_; lean_object* v_toCold_3183_; lean_object* v_env_3184_; lean_object* v_options_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3182_ = lean_st_ref_get(v___y_3180_);
v_toCold_3183_ = lean_ctor_get(v___y_3179_, 0);
v_env_3184_ = lean_ctor_get(v___x_3182_, 0);
lean_inc_ref(v_env_3184_);
lean_dec(v___x_3182_);
v_options_3185_ = lean_ctor_get(v_toCold_3183_, 2);
v___x_3186_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__1);
v___x_3187_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___closed__4);
lean_inc_ref(v_options_3185_);
v___x_3188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3188_, 0, v_env_3184_);
lean_ctor_set(v___x_3188_, 1, v___x_3186_);
lean_ctor_set(v___x_3188_, 2, v___x_3187_);
lean_ctor_set(v___x_3188_, 3, v_options_3185_);
v___x_3189_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
lean_ctor_set(v___x_3189_, 1, v_msgData_3178_);
v___x_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10___boxed(lean_object* v_msgData_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msgData_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(lean_object* v_msg_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_ref_3200_; lean_object* v___x_3201_; lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3210_; 
v_ref_3200_ = lean_ctor_get(v___y_3197_, 2);
v___x_3201_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3196_, v___y_3197_, v___y_3198_);
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3210_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3210_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___x_3208_; 
lean_inc(v_ref_3200_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_ref_3200_);
lean_ctor_set(v___x_3206_, 1, v_a_3202_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 1);
lean_ctor_set(v___x_3204_, 0, v___x_3206_);
v___x_3208_ = v___x_3204_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg___boxed(lean_object* v_msg_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3211_, v___y_3212_, v___y_3213_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
return v_res_3215_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0(void){
_start:
{
lean_object* v___x_3216_; double v___x_3217_; 
v___x_3216_ = lean_unsigned_to_nat(0u);
v___x_3217_ = lean_float_of_nat(v___x_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(lean_object* v_cls_3221_, lean_object* v_msg_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v_ref_3227_; lean_object* v___x_3228_; lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3274_; 
v_ref_3227_ = lean_ctor_get(v___y_3224_, 2);
v___x_3228_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3222_, v___y_3224_, v___y_3225_);
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3231_ = v___x_3228_;
v_isShared_3232_ = v_isSharedCheck_3274_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3228_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3274_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v_traceState_3234_; lean_object* v_env_3235_; lean_object* v_nextMacroScope_3236_; lean_object* v_ngen_3237_; lean_object* v_auxDeclNGen_3238_; lean_object* v_cache_3239_; lean_object* v_messages_3240_; lean_object* v_infoState_3241_; lean_object* v_snapshotTasks_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3273_; 
v___x_3233_ = lean_st_ref_take(v___y_3225_);
v_traceState_3234_ = lean_ctor_get(v___x_3233_, 4);
v_env_3235_ = lean_ctor_get(v___x_3233_, 0);
v_nextMacroScope_3236_ = lean_ctor_get(v___x_3233_, 1);
v_ngen_3237_ = lean_ctor_get(v___x_3233_, 2);
v_auxDeclNGen_3238_ = lean_ctor_get(v___x_3233_, 3);
v_cache_3239_ = lean_ctor_get(v___x_3233_, 5);
v_messages_3240_ = lean_ctor_get(v___x_3233_, 6);
v_infoState_3241_ = lean_ctor_get(v___x_3233_, 7);
v_snapshotTasks_3242_ = lean_ctor_get(v___x_3233_, 8);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3244_ = v___x_3233_;
v_isShared_3245_ = v_isSharedCheck_3273_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_snapshotTasks_3242_);
lean_inc(v_infoState_3241_);
lean_inc(v_messages_3240_);
lean_inc(v_cache_3239_);
lean_inc(v_traceState_3234_);
lean_inc(v_auxDeclNGen_3238_);
lean_inc(v_ngen_3237_);
lean_inc(v_nextMacroScope_3236_);
lean_inc(v_env_3235_);
lean_dec(v___x_3233_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3273_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
uint64_t v_tid_3246_; lean_object* v_traces_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3272_; 
v_tid_3246_ = lean_ctor_get_uint64(v_traceState_3234_, sizeof(void*)*1);
v_traces_3247_ = lean_ctor_get(v_traceState_3234_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_traceState_3234_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3249_ = v_traceState_3234_;
v_isShared_3250_ = v_isSharedCheck_3272_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_traces_3247_);
lean_dec(v_traceState_3234_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3272_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; double v___x_3253_; uint8_t v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3262_; 
v___x_3251_ = lean_box(0);
v___x_3252_ = lean_box(0);
v___x_3253_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3254_ = 0;
v___x_3255_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3256_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3256_, 0, v_cls_3221_);
lean_ctor_set(v___x_3256_, 1, v___x_3252_);
lean_ctor_set(v___x_3256_, 2, v___x_3255_);
lean_ctor_set_float(v___x_3256_, sizeof(void*)*3, v___x_3253_);
lean_ctor_set_float(v___x_3256_, sizeof(void*)*3 + 8, v___x_3253_);
lean_ctor_set_uint8(v___x_3256_, sizeof(void*)*3 + 16, v___x_3254_);
v___x_3257_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3258_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
lean_ctor_set(v___x_3258_, 1, v_a_3229_);
lean_ctor_set(v___x_3258_, 2, v___x_3257_);
lean_inc(v_ref_3227_);
v___x_3259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3259_, 0, v_ref_3227_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = l_Lean_PersistentArray_push___redArg(v_traces_3247_, v___x_3259_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3260_);
v___x_3262_ = v___x_3249_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3260_);
lean_ctor_set_uint64(v_reuseFailAlloc_3271_, sizeof(void*)*1, v_tid_3246_);
v___x_3262_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
lean_object* v___x_3264_; 
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 4, v___x_3262_);
v___x_3264_ = v___x_3244_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_env_3235_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_nextMacroScope_3236_);
lean_ctor_set(v_reuseFailAlloc_3270_, 2, v_ngen_3237_);
lean_ctor_set(v_reuseFailAlloc_3270_, 3, v_auxDeclNGen_3238_);
lean_ctor_set(v_reuseFailAlloc_3270_, 4, v___x_3262_);
lean_ctor_set(v_reuseFailAlloc_3270_, 5, v_cache_3239_);
lean_ctor_set(v_reuseFailAlloc_3270_, 6, v_messages_3240_);
lean_ctor_set(v_reuseFailAlloc_3270_, 7, v_infoState_3241_);
lean_ctor_set(v_reuseFailAlloc_3270_, 8, v_snapshotTasks_3242_);
v___x_3264_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3265_ = lean_st_ref_put(v___y_3225_, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3251_);
lean_ctor_set(v___x_3266_, 1, v___y_3223_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v___x_3266_);
v___x_3268_ = v___x_3231_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___boxed(lean_object* v_cls_3275_, lean_object* v_msg_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3275_, v_msg_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(lean_object* v_a_3282_, lean_object* v_x_3283_){
_start:
{
if (lean_obj_tag(v_x_3283_) == 0)
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_box(0);
return v___x_3284_;
}
else
{
lean_object* v_key_3285_; lean_object* v_value_3286_; lean_object* v_tail_3287_; uint8_t v___x_3288_; 
v_key_3285_ = lean_ctor_get(v_x_3283_, 0);
v_value_3286_ = lean_ctor_get(v_x_3283_, 1);
v_tail_3287_ = lean_ctor_get(v_x_3283_, 2);
v___x_3288_ = l_Lean_instBEqFVarId_beq(v_key_3285_, v_a_3282_);
if (v___x_3288_ == 0)
{
v_x_3283_ = v_tail_3287_;
goto _start;
}
else
{
lean_object* v___x_3290_; 
lean_inc(v_value_3286_);
v___x_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3290_, 0, v_value_3286_);
return v___x_3290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_3291_, lean_object* v_x_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3291_, v_x_3292_);
lean_dec(v_x_3292_);
lean_dec(v_a_3291_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(lean_object* v_m_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_buckets_3296_; lean_object* v___x_3297_; uint64_t v___x_3298_; uint64_t v___x_3299_; uint64_t v___x_3300_; uint64_t v_fold_3301_; uint64_t v___x_3302_; uint64_t v___x_3303_; uint64_t v___x_3304_; size_t v___x_3305_; size_t v___x_3306_; size_t v___x_3307_; size_t v___x_3308_; size_t v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_buckets_3296_ = lean_ctor_get(v_m_3294_, 1);
v___x_3297_ = lean_array_get_size(v_buckets_3296_);
v___x_3298_ = l_Lean_instHashableFVarId_hash(v_a_3295_);
v___x_3299_ = 32ULL;
v___x_3300_ = lean_uint64_shift_right(v___x_3298_, v___x_3299_);
v_fold_3301_ = lean_uint64_xor(v___x_3298_, v___x_3300_);
v___x_3302_ = 16ULL;
v___x_3303_ = lean_uint64_shift_right(v_fold_3301_, v___x_3302_);
v___x_3304_ = lean_uint64_xor(v_fold_3301_, v___x_3303_);
v___x_3305_ = lean_uint64_to_usize(v___x_3304_);
v___x_3306_ = lean_usize_of_nat(v___x_3297_);
v___x_3307_ = ((size_t)1ULL);
v___x_3308_ = lean_usize_sub(v___x_3306_, v___x_3307_);
v___x_3309_ = lean_usize_land(v___x_3305_, v___x_3308_);
v___x_3310_ = lean_array_uget_borrowed(v_buckets_3296_, v___x_3309_);
v___x_3311_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3295_, v___x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg___boxed(lean_object* v_m_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3312_, v_a_3313_);
lean_dec(v_a_3313_);
lean_dec_ref(v_m_3312_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed(lean_object* v___x_3315_, lean_object* v_m_3316_, lean_object* v_e_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
uint8_t v___x_17671__boxed_3322_; lean_object* v_res_3323_; 
v___x_17671__boxed_3322_ = lean_unbox(v___x_3315_);
v_res_3323_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(v___x_17671__boxed_3322_, v_m_3316_, v_e_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v_e_3317_);
return v_res_3323_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = lean_box(0);
v___x_3325_ = lean_unsigned_to_nat(16u);
v___x_3326_ = lean_mk_array(v___x_3325_, v___x_3324_);
return v___x_3326_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1(void){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3327_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__0);
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
lean_ctor_set(v___x_3329_, 1, v___x_3327_);
return v___x_3329_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5(void){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3333_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__4));
v___x_3334_ = lean_unsigned_to_nat(4u);
v___x_3335_ = lean_unsigned_to_nat(384u);
v___x_3336_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__3));
v___x_3337_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3338_ = l_mkPanicMessageWithDecl(v___x_3337_, v___x_3336_, v___x_3335_, v___x_3334_, v___x_3333_);
return v___x_3338_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__6));
v___x_3341_ = l_Lean_stringToMessageData(v___x_3340_);
return v___x_3341_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3351_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__12));
v___x_3352_ = l_Lean_Name_append(v___x_3351_, v___x_3350_);
return v___x_3352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15(void){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3354_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__14));
v___x_3355_ = l_Lean_stringToMessageData(v___x_3354_);
return v___x_3355_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17(void){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__16));
v___x_3358_ = l_Lean_stringToMessageData(v___x_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(lean_object* v_m_3359_, lean_object* v_fvarId_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3359_, v_fvarId_3360_);
if (lean_obj_tag(v___x_3365_) == 1)
{
lean_object* v_val_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3480_; 
v_val_3366_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3368_ = v___x_3365_;
v_isShared_3369_ = v_isSharedCheck_3480_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_val_3366_);
lean_dec(v___x_3365_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3480_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v_fst_3370_; lean_object* v_snd_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3479_; 
v_fst_3370_ = lean_ctor_get(v_val_3366_, 0);
v_snd_3371_ = lean_ctor_get(v_val_3366_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_val_3366_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3373_ = v_val_3366_;
v_isShared_3374_ = v_isSharedCheck_3479_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_snd_3371_);
lean_inc(v_fst_3370_);
lean_dec(v_val_3366_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3479_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v_tempMark_3375_; lean_object* v_doneMark_3376_; lean_object* v___x_3377_; uint8_t v___x_3378_; 
v_tempMark_3375_ = lean_ctor_get(v_a_3361_, 0);
v_doneMark_3376_ = lean_ctor_get(v_a_3361_, 1);
v___x_3377_ = l_Lean_LocalDecl_fvarId(v_fst_3370_);
v___x_3378_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_doneMark_3376_, v___x_3377_);
if (v___x_3378_ == 0)
{
lean_object* v_toCold_3379_; lean_object* v_options_3380_; lean_object* v_inheritedTraceOptions_3381_; uint8_t v_hasTrace_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; lean_object* v___f_3385_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3447_; lean_object* v_tempMark_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; 
lean_del_object(v___x_3373_);
lean_del_object(v___x_3368_);
v_toCold_3379_ = lean_ctor_get(v_a_3362_, 0);
v_options_3380_ = lean_ctor_get(v_toCold_3379_, 2);
v_inheritedTraceOptions_3381_ = lean_ctor_get(v_toCold_3379_, 11);
v_hasTrace_3382_ = lean_ctor_get_uint8(v_options_3380_, sizeof(void*)*1);
v___x_3383_ = 1;
v___x_3384_ = lean_box(v___x_3383_);
v___f_3385_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3385_, 0, v___x_3384_);
lean_closure_set(v___f_3385_, 1, v_m_3359_);
if (v_hasTrace_3382_ == 0)
{
lean_inc_ref(v_tempMark_3375_);
v___y_3447_ = v_a_3361_;
v_tempMark_3448_ = v_tempMark_3375_;
v___y_3449_ = v_a_3362_;
v___y_3450_ = v_a_3363_;
goto v___jp_3446_;
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3456_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_3457_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_3458_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3381_, v_options_3380_, v___x_3457_);
if (v___x_3458_ == 0)
{
lean_inc_ref(v_tempMark_3375_);
v___y_3447_ = v_a_3361_;
v_tempMark_3448_ = v_tempMark_3375_;
v___y_3449_ = v_a_3362_;
v___y_3450_ = v_a_3363_;
goto v___jp_3446_;
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3459_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__15);
lean_inc(v___x_3377_);
v___x_3460_ = l_Lean_mkFVar(v___x_3377_);
v___x_3461_ = l_Lean_MessageData_ofExpr(v___x_3460_);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3459_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__17);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3462_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = l_Lean_LocalDecl_type(v_fst_3370_);
v___x_3466_ = l_Lean_MessageData_ofExpr(v___x_3465_);
v___x_3467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3464_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
v___x_3468_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v___x_3456_, v___x_3467_, v_a_3361_, v_a_3362_, v_a_3363_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; lean_object* v_snd_3470_; lean_object* v_tempMark_3471_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_a_3469_);
lean_dec_ref_known(v___x_3468_, 1);
v_snd_3470_ = lean_ctor_get(v_a_3469_, 1);
lean_inc(v_snd_3470_);
lean_dec(v_a_3469_);
v_tempMark_3471_ = lean_ctor_get(v_snd_3470_, 0);
lean_inc_ref(v_tempMark_3471_);
v___y_3447_ = v_snd_3470_;
v_tempMark_3448_ = v_tempMark_3471_;
v___y_3449_ = v_a_3362_;
v___y_3450_ = v_a_3363_;
goto v___jp_3446_;
}
else
{
lean_dec_ref(v___f_3385_);
lean_dec(v___x_3377_);
lean_dec(v_snd_3371_);
lean_dec(v_fst_3370_);
return v___x_3468_;
}
}
}
v___jp_3386_:
{
lean_object* v_tempMark_3390_; lean_object* v_doneMark_3391_; lean_object* v_newDecls_3392_; lean_object* v_newArgs_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3438_; 
v_tempMark_3390_ = lean_ctor_get(v___y_3389_, 0);
v_doneMark_3391_ = lean_ctor_get(v___y_3389_, 1);
v_newDecls_3392_ = lean_ctor_get(v___y_3389_, 2);
v_newArgs_3393_ = lean_ctor_get(v___y_3389_, 3);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___y_3389_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3395_ = v___y_3389_;
v_isShared_3396_ = v_isSharedCheck_3438_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_newArgs_3393_);
lean_inc(v_newDecls_3392_);
lean_inc(v_doneMark_3391_);
lean_inc(v_tempMark_3390_);
lean_dec(v___y_3389_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3438_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3400_; 
v___x_3397_ = lean_box(0);
lean_inc(v___x_3377_);
v___x_3398_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_tempMark_3390_, v___x_3377_, v___x_3397_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v___x_3398_);
v___x_3400_ = v___x_3395_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_doneMark_3391_);
lean_ctor_set(v_reuseFailAlloc_3437_, 2, v_newDecls_3392_);
lean_ctor_set(v_reuseFailAlloc_3437_, 3, v_newArgs_3393_);
v___x_3400_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3401_ = l_Lean_LocalDecl_type(v_fst_3370_);
v___x_3402_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__1);
v___x_3403_ = lean_st_mk_ref(v___x_3402_);
v___x_3404_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3(v___f_3385_, v___x_3401_, v___x_3403_, v___x_3400_, v___y_3387_, v___y_3388_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3436_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3436_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3436_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v_snd_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3434_; 
v_snd_3409_ = lean_ctor_get(v_a_3405_, 1);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_a_3405_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; 
v_unused_3435_ = lean_ctor_get(v_a_3405_, 0);
lean_dec(v_unused_3435_);
v___x_3411_ = v_a_3405_;
v_isShared_3412_ = v_isSharedCheck_3434_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_snd_3409_);
lean_dec(v_a_3405_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3434_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; lean_object* v_tempMark_3414_; lean_object* v_doneMark_3415_; lean_object* v_newDecls_3416_; lean_object* v_newArgs_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3433_; 
v___x_3413_ = lean_st_ref_get(v___x_3403_);
lean_dec(v___x_3403_);
lean_dec(v___x_3413_);
v_tempMark_3414_ = lean_ctor_get(v_snd_3409_, 0);
v_doneMark_3415_ = lean_ctor_get(v_snd_3409_, 1);
v_newDecls_3416_ = lean_ctor_get(v_snd_3409_, 2);
v_newArgs_3417_ = lean_ctor_get(v_snd_3409_, 3);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_snd_3409_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3419_ = v_snd_3409_;
v_isShared_3420_ = v_isSharedCheck_3433_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_newArgs_3417_);
lean_inc(v_newDecls_3416_);
lean_inc(v_doneMark_3415_);
lean_inc(v_tempMark_3414_);
lean_dec(v_snd_3409_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3433_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3421_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_doneMark_3415_, v___x_3377_, v___x_3397_);
v___x_3422_ = lean_array_push(v_newDecls_3416_, v_fst_3370_);
v___x_3423_ = lean_array_push(v_newArgs_3417_, v_snd_3371_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 3, v___x_3423_);
lean_ctor_set(v___x_3419_, 2, v___x_3422_);
lean_ctor_set(v___x_3419_, 1, v___x_3421_);
v___x_3425_ = v___x_3419_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_tempMark_3414_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v___x_3421_);
lean_ctor_set(v_reuseFailAlloc_3432_, 2, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3432_, 3, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3427_; 
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 1, v___x_3425_);
lean_ctor_set(v___x_3411_, 0, v___x_3397_);
v___x_3427_ = v___x_3411_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3429_; 
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3427_);
v___x_3429_ = v___x_3407_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3403_);
lean_dec(v___x_3377_);
lean_dec(v_snd_3371_);
lean_dec(v_fst_3370_);
return v___x_3404_;
}
}
}
}
v___jp_3439_:
{
uint8_t v___x_3443_; 
v___x_3443_ = l_Lean_LocalDecl_isLet(v_fst_3370_, v___x_3383_);
if (v___x_3443_ == 0)
{
v___y_3387_ = v___y_3441_;
v___y_3388_ = v___y_3442_;
v___y_3389_ = v___y_3440_;
goto v___jp_3386_;
}
else
{
if (v___x_3378_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_dec_ref(v___f_3385_);
lean_dec(v___x_3377_);
lean_dec(v_snd_3371_);
lean_dec(v_fst_3370_);
v___x_3444_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__5);
v___x_3445_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__4(v___x_3444_, v___y_3440_, v___y_3441_, v___y_3442_);
return v___x_3445_;
}
else
{
v___y_3387_ = v___y_3441_;
v___y_3388_ = v___y_3442_;
v___y_3389_ = v___y_3440_;
goto v___jp_3386_;
}
}
}
v___jp_3446_:
{
uint8_t v___x_3451_; 
v___x_3451_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_tempMark_3448_, v___x_3377_);
lean_dec_ref(v_tempMark_3448_);
if (v___x_3451_ == 0)
{
v___y_3440_ = v___y_3447_;
v___y_3441_ = v___y_3449_;
v___y_3442_ = v___y_3450_;
goto v___jp_3439_;
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec_ref(v___y_3447_);
v___x_3452_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__7);
v___x_3453_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v___x_3452_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v_snd_3455_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v_snd_3455_ = lean_ctor_get(v_a_3454_, 1);
lean_inc(v_snd_3455_);
lean_dec(v_a_3454_);
v___y_3440_ = v_snd_3455_;
v___y_3441_ = v___y_3449_;
v___y_3442_ = v___y_3450_;
goto v___jp_3439_;
}
else
{
lean_dec_ref(v___f_3385_);
lean_dec(v___x_3377_);
lean_dec(v_snd_3371_);
lean_dec(v_fst_3370_);
return v___x_3453_;
}
}
}
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3474_; 
lean_dec(v___x_3377_);
lean_dec(v_snd_3371_);
lean_dec(v_fst_3370_);
lean_dec_ref(v_m_3359_);
v___x_3472_ = lean_box(0);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 1, v_a_3361_);
lean_ctor_set(v___x_3373_, 0, v___x_3472_);
v___x_3474_ = v___x_3373_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3472_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_a_3361_);
v___x_3474_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3476_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set_tag(v___x_3368_, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3474_);
v___x_3476_ = v___x_3368_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
}
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_dec(v___x_3365_);
lean_dec_ref(v_m_3359_);
v___x_3481_ = lean_box(0);
v___x_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
lean_ctor_set(v___x_3482_, 1, v_a_3361_);
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
return v___x_3483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___lam__0(uint8_t v___x_3484_, lean_object* v_m_3485_, lean_object* v_e_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v___y_3492_; uint8_t v___x_3496_; 
v___x_3496_ = l_Lean_Expr_hasFVar(v_e_3486_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_dec_ref(v_m_3485_);
v___x_3497_ = lean_box(v___x_3496_);
v___x_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
lean_ctor_set(v___x_3498_, 1, v___y_3487_);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
else
{
uint8_t v___x_3500_; 
v___x_3500_ = l_Lean_Expr_isFVar(v_e_3486_);
if (v___x_3500_ == 0)
{
lean_dec_ref(v_m_3485_);
v___y_3492_ = v___y_3487_;
goto v___jp_3491_;
}
else
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = l_Lean_Expr_fvarId_x21(v_e_3486_);
v___x_3502_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3485_, v___x_3501_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___x_3501_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v_snd_3504_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v_snd_3504_ = lean_ctor_get(v_a_3503_, 1);
lean_inc(v_snd_3504_);
lean_dec(v_a_3503_);
v___y_3492_ = v_snd_3504_;
goto v___jp_3491_;
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
v_a_3505_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3502_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3502_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
v___jp_3491_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3493_ = lean_box(v___x_3484_);
v___x_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v___y_3492_);
v___x_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
return v___x_3495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___boxed(lean_object* v_m_3513_, lean_object* v_fvarId_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v_m_3513_, v_fvarId_3514_, v_a_3515_, v_a_3516_, v_a_3517_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_fvarId_3514_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(lean_object* v_00_u03b2_3520_, lean_object* v_m_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___redArg(v_m_3521_, v_a_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0___boxed(lean_object* v_00_u03b2_3524_, lean_object* v_m_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0(v_00_u03b2_3524_, v_m_3525_, v_a_3526_);
lean_dec(v_a_3526_);
lean_dec_ref(v_m_3525_);
return v_res_3527_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(lean_object* v_00_u03b2_3528_, lean_object* v_m_3529_, lean_object* v_a_3530_){
_start:
{
uint8_t v___x_3531_; 
v___x_3531_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___redArg(v_m_3529_, v_a_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1___boxed(lean_object* v_00_u03b2_3532_, lean_object* v_m_3533_, lean_object* v_a_3534_){
_start:
{
uint8_t v_res_3535_; lean_object* v_r_3536_; 
v_res_3535_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1(v_00_u03b2_3532_, v_m_3533_, v_a_3534_);
lean_dec(v_a_3534_);
lean_dec_ref(v_m_3533_);
v_r_3536_ = lean_box(v_res_3535_);
return v_r_3536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2(lean_object* v_00_u03b2_3537_, lean_object* v_m_3538_, lean_object* v_a_3539_, lean_object* v_b_3540_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2___redArg(v_m_3538_, v_a_3539_, v_b_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(lean_object* v_00_u03b1_3542_, lean_object* v_msg_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___redArg(v_msg_3543_, v___y_3545_, v___y_3546_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5___boxed(lean_object* v_00_u03b1_3549_, lean_object* v_msg_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5(v_00_u03b1_3549_, v_msg_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec_ref(v___y_3551_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(lean_object* v_00_u03b2_3556_, lean_object* v_a_3557_, lean_object* v_x_3558_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___redArg(v_a_3557_, v_x_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3560_, lean_object* v_a_3561_, lean_object* v_x_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__0_spec__0(v_00_u03b2_3560_, v_a_3561_, v_x_3562_);
lean_dec(v_x_3562_);
lean_dec(v_a_3561_);
return v_res_3563_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(lean_object* v_00_u03b2_3564_, lean_object* v_a_3565_, lean_object* v_x_3566_){
_start:
{
uint8_t v___x_3567_; 
v___x_3567_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3565_, v_x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3568_, lean_object* v_a_3569_, lean_object* v_x_3570_){
_start:
{
uint8_t v_res_3571_; lean_object* v_r_3572_; 
v_res_3571_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2(v_00_u03b2_3568_, v_a_3569_, v_x_3570_);
lean_dec(v_x_3570_);
lean_dec(v_a_3569_);
v_r_3572_ = lean_box(v_res_3571_);
return v_r_3572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4(lean_object* v_00_u03b2_3573_, lean_object* v_data_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_data_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(lean_object* v_00_u03b2_3576_, lean_object* v_m_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___redArg(v_m_3577_, v_a_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3580_, lean_object* v_m_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6(v_00_u03b2_3580_, v_m_3581_, v_a_3582_);
lean_dec_ref(v_a_3582_);
lean_dec_ref(v_m_3581_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7(lean_object* v_00_u03b2_3584_, lean_object* v_m_3585_, lean_object* v_a_3586_, lean_object* v_b_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7___redArg(v_m_3585_, v_a_3586_, v_b_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_3589_, lean_object* v_i_3590_, lean_object* v_source_3591_, lean_object* v_target_3592_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6___redArg(v_i_3590_, v_source_3591_, v_target_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_3594_, lean_object* v_a_3595_, lean_object* v_x_3596_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___redArg(v_a_3595_, v_x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3598_, lean_object* v_a_3599_, lean_object* v_x_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__6_spec__9(v_00_u03b2_3598_, v_a_3599_, v_x_3600_);
lean_dec(v_x_3600_);
lean_dec_ref(v_a_3599_);
return v_res_3601_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3602_, lean_object* v_a_3603_, lean_object* v_x_3604_){
_start:
{
uint8_t v___x_3605_; 
v___x_3605_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___redArg(v_a_3603_, v_x_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3606_, lean_object* v_a_3607_, lean_object* v_x_3608_){
_start:
{
uint8_t v_res_3609_; lean_object* v_r_3610_; 
v_res_3609_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__11(v_00_u03b2_3606_, v_a_3607_, v_x_3608_);
lean_dec(v_x_3608_);
lean_dec_ref(v_a_3607_);
v_r_3610_ = lean_box(v_res_3609_);
return v_r_3610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b2_3611_, lean_object* v_data_3612_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12___redArg(v_data_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13(lean_object* v_00_u03b2_3614_, lean_object* v_a_3615_, lean_object* v_b_3616_, lean_object* v_x_3617_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__13___redArg(v_a_3615_, v_b_3616_, v_x_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_3619_, lean_object* v_x_3620_, lean_object* v_x_3621_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4_spec__6_spec__11___redArg(v_x_3620_, v_x_3621_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17(lean_object* v_00_u03b2_3623_, lean_object* v_i_3624_, lean_object* v_source_3625_, lean_object* v_target_3626_){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17___redArg(v_i_3624_, v_source_3625_, v_target_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18(lean_object* v_00_u03b2_3628_, lean_object* v_x_3629_, lean_object* v_x_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__3_spec__7_spec__12_spec__17_spec__18___redArg(v_x_3629_, v_x_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(lean_object* v_msg_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v___f_3637_; lean_object* v___x_7386__overap_3638_; lean_object* v___x_3639_; 
v___f_3637_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___closed__0));
v___x_7386__overap_3638_ = lean_panic_fn_borrowed(v___f_3637_, v_msg_3633_);
lean_inc(v___y_3635_);
lean_inc_ref(v___y_3634_);
v___x_3639_ = lean_apply_3(v___x_7386__overap_3638_, v___y_3634_, v___y_3635_, lean_box(0));
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1___boxed(lean_object* v_msg_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v_msg_3640_, v___y_3641_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(lean_object* v_newDecls_3645_, lean_object* v_newArgs_3646_, lean_object* v_____r_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3652_, 0, v_newDecls_3645_);
lean_ctor_set(v___x_3652_, 1, v_newArgs_3646_);
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
lean_ctor_set(v___x_3653_, 1, v___y_3648_);
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed(lean_object* v_newDecls_3655_, lean_object* v_newArgs_3656_, lean_object* v_____r_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_3655_, v_newArgs_3656_, v_____r_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(lean_object* v_cls_3663_, lean_object* v_msg_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v_ref_3668_; lean_object* v___x_3669_; lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3714_; 
v_ref_3668_ = lean_ctor_get(v___y_3665_, 2);
v___x_3669_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__5_spec__10(v_msg_3664_, v___y_3665_, v___y_3666_);
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3714_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3714_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; lean_object* v_traceState_3675_; lean_object* v_env_3676_; lean_object* v_nextMacroScope_3677_; lean_object* v_ngen_3678_; lean_object* v_auxDeclNGen_3679_; lean_object* v_cache_3680_; lean_object* v_messages_3681_; lean_object* v_infoState_3682_; lean_object* v_snapshotTasks_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3713_; 
v___x_3674_ = lean_st_ref_take(v___y_3666_);
v_traceState_3675_ = lean_ctor_get(v___x_3674_, 4);
v_env_3676_ = lean_ctor_get(v___x_3674_, 0);
v_nextMacroScope_3677_ = lean_ctor_get(v___x_3674_, 1);
v_ngen_3678_ = lean_ctor_get(v___x_3674_, 2);
v_auxDeclNGen_3679_ = lean_ctor_get(v___x_3674_, 3);
v_cache_3680_ = lean_ctor_get(v___x_3674_, 5);
v_messages_3681_ = lean_ctor_get(v___x_3674_, 6);
v_infoState_3682_ = lean_ctor_get(v___x_3674_, 7);
v_snapshotTasks_3683_ = lean_ctor_get(v___x_3674_, 8);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3685_ = v___x_3674_;
v_isShared_3686_ = v_isSharedCheck_3713_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_snapshotTasks_3683_);
lean_inc(v_infoState_3682_);
lean_inc(v_messages_3681_);
lean_inc(v_cache_3680_);
lean_inc(v_traceState_3675_);
lean_inc(v_auxDeclNGen_3679_);
lean_inc(v_ngen_3678_);
lean_inc(v_nextMacroScope_3677_);
lean_inc(v_env_3676_);
lean_dec(v___x_3674_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3713_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
uint64_t v_tid_3687_; lean_object* v_traces_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3712_; 
v_tid_3687_ = lean_ctor_get_uint64(v_traceState_3675_, sizeof(void*)*1);
v_traces_3688_ = lean_ctor_get(v_traceState_3675_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_traceState_3675_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3690_ = v_traceState_3675_;
v_isShared_3691_ = v_isSharedCheck_3712_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_traces_3688_);
lean_dec(v_traceState_3675_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3712_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; double v___x_3694_; uint8_t v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3692_ = lean_box(0);
v___x_3693_ = lean_box(0);
v___x_3694_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__0);
v___x_3695_ = 0;
v___x_3696_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__1));
v___x_3697_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3697_, 0, v_cls_3663_);
lean_ctor_set(v___x_3697_, 1, v___x_3693_);
lean_ctor_set(v___x_3697_, 2, v___x_3696_);
lean_ctor_set_float(v___x_3697_, sizeof(void*)*3, v___x_3694_);
lean_ctor_set_float(v___x_3697_, sizeof(void*)*3 + 8, v___x_3694_);
lean_ctor_set_uint8(v___x_3697_, sizeof(void*)*3 + 16, v___x_3695_);
v___x_3698_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6___closed__2));
v___x_3699_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3697_);
lean_ctor_set(v___x_3699_, 1, v_a_3670_);
lean_ctor_set(v___x_3699_, 2, v___x_3698_);
lean_inc(v_ref_3668_);
v___x_3700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3700_, 0, v_ref_3668_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
v___x_3701_ = l_Lean_PersistentArray_push___redArg(v_traces_3688_, v___x_3700_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 0, v___x_3701_);
v___x_3703_ = v___x_3690_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3701_);
lean_ctor_set_uint64(v_reuseFailAlloc_3711_, sizeof(void*)*1, v_tid_3687_);
v___x_3703_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
lean_object* v___x_3705_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 4, v___x_3703_);
v___x_3705_ = v___x_3685_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_env_3676_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_nextMacroScope_3677_);
lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_ngen_3678_);
lean_ctor_set(v_reuseFailAlloc_3710_, 3, v_auxDeclNGen_3679_);
lean_ctor_set(v_reuseFailAlloc_3710_, 4, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3710_, 5, v_cache_3680_);
lean_ctor_set(v_reuseFailAlloc_3710_, 6, v_messages_3681_);
lean_ctor_set(v_reuseFailAlloc_3710_, 7, v_infoState_3682_);
lean_ctor_set(v_reuseFailAlloc_3710_, 8, v_snapshotTasks_3683_);
v___x_3705_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3706_; lean_object* v___x_3708_; 
v___x_3706_ = lean_st_ref_put(v___y_3666_, v___x_3705_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3692_);
v___x_3708_ = v___x_3672_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3692_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6___boxed(lean_object* v_cls_3715_, lean_object* v_msg_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3715_, v_msg_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(size_t v_sz_3721_, size_t v_i_3722_, lean_object* v_bs_3723_){
_start:
{
uint8_t v___x_3724_; 
v___x_3724_ = lean_usize_dec_lt(v_i_3722_, v_sz_3721_);
if (v___x_3724_ == 0)
{
return v_bs_3723_;
}
else
{
lean_object* v_v_3725_; lean_object* v___x_3726_; lean_object* v_bs_x27_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; size_t v___x_3730_; size_t v___x_3731_; lean_object* v___x_3732_; 
v_v_3725_ = lean_array_uget(v_bs_3723_, v_i_3722_);
v___x_3726_ = lean_unsigned_to_nat(0u);
v_bs_x27_3727_ = lean_array_uset(v_bs_3723_, v_i_3722_, v___x_3726_);
v___x_3728_ = l_Lean_LocalDecl_fvarId(v_v_3725_);
lean_dec(v_v_3725_);
v___x_3729_ = l_Lean_mkFVar(v___x_3728_);
v___x_3730_ = ((size_t)1ULL);
v___x_3731_ = lean_usize_add(v_i_3722_, v___x_3730_);
v___x_3732_ = lean_array_uset(v_bs_x27_3727_, v_i_3722_, v___x_3729_);
v_i_3722_ = v___x_3731_;
v_bs_3723_ = v___x_3732_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4___boxed(lean_object* v_sz_3734_, lean_object* v_i_3735_, lean_object* v_bs_3736_){
_start:
{
size_t v_sz_boxed_3737_; size_t v_i_boxed_3738_; lean_object* v_res_3739_; 
v_sz_boxed_3737_ = lean_unbox_usize(v_sz_3734_);
lean_dec(v_sz_3734_);
v_i_boxed_3738_ = lean_unbox_usize(v_i_3735_);
lean_dec(v_i_3735_);
v_res_3739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_boxed_3737_, v_i_boxed_3738_, v_bs_3736_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(lean_object* v___x_3740_, lean_object* v_as_3741_, size_t v_sz_3742_, size_t v_i_3743_, lean_object* v_b_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
uint8_t v___x_3749_; 
v___x_3749_ = lean_usize_dec_lt(v_i_3743_, v_sz_3742_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
lean_dec_ref(v___x_3740_);
v___x_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3750_, 0, v_b_3744_);
lean_ctor_set(v___x_3750_, 1, v___y_3745_);
v___x_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
return v___x_3751_;
}
else
{
lean_object* v___x_3752_; lean_object* v_a_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3752_ = lean_box(0);
v_a_3753_ = lean_array_uget_borrowed(v_as_3741_, v_i_3743_);
v___x_3754_ = l_Lean_LocalDecl_fvarId(v_a_3753_);
lean_inc_ref(v___x_3740_);
v___x_3755_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit(v___x_3740_, v___x_3754_, v___y_3745_, v___y_3746_, v___y_3747_);
lean_dec(v___x_3754_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v_snd_3757_; size_t v___x_3758_; size_t v___x_3759_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3755_, 1);
v_snd_3757_ = lean_ctor_get(v_a_3756_, 1);
lean_inc(v_snd_3757_);
lean_dec(v_a_3756_);
v___x_3758_ = ((size_t)1ULL);
v___x_3759_ = lean_usize_add(v_i_3743_, v___x_3758_);
v_i_3743_ = v___x_3759_;
v_b_3744_ = v___x_3752_;
v___y_3745_ = v_snd_3757_;
goto _start;
}
else
{
lean_dec_ref(v___x_3740_);
return v___x_3755_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3___boxed(lean_object* v___x_3761_, lean_object* v_as_3762_, lean_object* v_sz_3763_, lean_object* v_i_3764_, lean_object* v_b_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
size_t v_sz_boxed_3770_; size_t v_i_boxed_3771_; lean_object* v_res_3772_; 
v_sz_boxed_3770_ = lean_unbox_usize(v_sz_3763_);
lean_dec(v_sz_3763_);
v_i_boxed_3771_ = lean_unbox_usize(v_i_3764_);
lean_dec(v_i_3764_);
v_res_3772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v___x_3761_, v_as_3762_, v_sz_boxed_3770_, v_i_boxed_3771_, v_b_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec_ref(v_as_3762_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
if (lean_obj_tag(v_a_3773_) == 0)
{
lean_object* v___x_3775_; 
v___x_3775_ = l_List_reverse___redArg(v_a_3774_);
return v___x_3775_;
}
else
{
lean_object* v_head_3776_; lean_object* v_tail_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3786_; 
v_head_3776_ = lean_ctor_get(v_a_3773_, 0);
v_tail_3777_ = lean_ctor_get(v_a_3773_, 1);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_a_3773_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3779_ = v_a_3773_;
v_isShared_3780_ = v_isSharedCheck_3786_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_tail_3777_);
lean_inc(v_head_3776_);
lean_dec(v_a_3773_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3786_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3781_ = l_Lean_MessageData_ofExpr(v_head_3776_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 1, v_a_3774_);
lean_ctor_set(v___x_3779_, 0, v___x_3781_);
v___x_3783_ = v___x_3779_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3781_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v_a_3774_);
v___x_3783_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
v_a_3773_ = v_tail_3777_;
v_a_3774_ = v___x_3783_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(lean_object* v_a_3787_, lean_object* v_b_3788_, lean_object* v_x_3789_){
_start:
{
if (lean_obj_tag(v_x_3789_) == 0)
{
lean_dec(v_b_3788_);
lean_dec(v_a_3787_);
return v_x_3789_;
}
else
{
lean_object* v_key_3790_; lean_object* v_value_3791_; lean_object* v_tail_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3804_; 
v_key_3790_ = lean_ctor_get(v_x_3789_, 0);
v_value_3791_ = lean_ctor_get(v_x_3789_, 1);
v_tail_3792_ = lean_ctor_get(v_x_3789_, 2);
v_isSharedCheck_3804_ = !lean_is_exclusive(v_x_3789_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3794_ = v_x_3789_;
v_isShared_3795_ = v_isSharedCheck_3804_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_tail_3792_);
lean_inc(v_value_3791_);
lean_inc(v_key_3790_);
lean_dec(v_x_3789_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3804_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
uint8_t v___x_3796_; 
v___x_3796_ = l_Lean_instBEqFVarId_beq(v_key_3790_, v_a_3787_);
if (v___x_3796_ == 0)
{
lean_object* v___x_3797_; lean_object* v___x_3799_; 
v___x_3797_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_3787_, v_b_3788_, v_tail_3792_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 2, v___x_3797_);
v___x_3799_ = v___x_3794_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_key_3790_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_value_3791_);
lean_ctor_set(v_reuseFailAlloc_3800_, 2, v___x_3797_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
else
{
lean_object* v___x_3802_; 
lean_dec(v_value_3791_);
lean_dec(v_key_3790_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 1, v_b_3788_);
lean_ctor_set(v___x_3794_, 0, v_a_3787_);
v___x_3802_ = v___x_3794_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3787_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v_b_3788_);
lean_ctor_set(v_reuseFailAlloc_3803_, 2, v_tail_3792_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(lean_object* v_m_3805_, lean_object* v_a_3806_, lean_object* v_b_3807_){
_start:
{
lean_object* v_size_3808_; lean_object* v_buckets_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3852_; 
v_size_3808_ = lean_ctor_get(v_m_3805_, 0);
v_buckets_3809_ = lean_ctor_get(v_m_3805_, 1);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_m_3805_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3811_ = v_m_3805_;
v_isShared_3812_ = v_isSharedCheck_3852_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_buckets_3809_);
lean_inc(v_size_3808_);
lean_dec(v_m_3805_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3852_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; uint64_t v___x_3814_; uint64_t v___x_3815_; uint64_t v___x_3816_; uint64_t v_fold_3817_; uint64_t v___x_3818_; uint64_t v___x_3819_; uint64_t v___x_3820_; size_t v___x_3821_; size_t v___x_3822_; size_t v___x_3823_; size_t v___x_3824_; size_t v___x_3825_; lean_object* v_bkt_3826_; uint8_t v___x_3827_; 
v___x_3813_ = lean_array_get_size(v_buckets_3809_);
v___x_3814_ = l_Lean_instHashableFVarId_hash(v_a_3806_);
v___x_3815_ = 32ULL;
v___x_3816_ = lean_uint64_shift_right(v___x_3814_, v___x_3815_);
v_fold_3817_ = lean_uint64_xor(v___x_3814_, v___x_3816_);
v___x_3818_ = 16ULL;
v___x_3819_ = lean_uint64_shift_right(v_fold_3817_, v___x_3818_);
v___x_3820_ = lean_uint64_xor(v_fold_3817_, v___x_3819_);
v___x_3821_ = lean_uint64_to_usize(v___x_3820_);
v___x_3822_ = lean_usize_of_nat(v___x_3813_);
v___x_3823_ = ((size_t)1ULL);
v___x_3824_ = lean_usize_sub(v___x_3822_, v___x_3823_);
v___x_3825_ = lean_usize_land(v___x_3821_, v___x_3824_);
v_bkt_3826_ = lean_array_uget_borrowed(v_buckets_3809_, v___x_3825_);
v___x_3827_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__1_spec__2___redArg(v_a_3806_, v_bkt_3826_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; lean_object* v_size_x27_3829_; lean_object* v___x_3830_; lean_object* v_buckets_x27_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; uint8_t v___x_3837_; 
v___x_3828_ = lean_unsigned_to_nat(1u);
v_size_x27_3829_ = lean_nat_add(v_size_3808_, v___x_3828_);
lean_dec(v_size_3808_);
lean_inc(v_bkt_3826_);
v___x_3830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3830_, 0, v_a_3806_);
lean_ctor_set(v___x_3830_, 1, v_b_3807_);
lean_ctor_set(v___x_3830_, 2, v_bkt_3826_);
v_buckets_x27_3831_ = lean_array_uset(v_buckets_3809_, v___x_3825_, v___x_3830_);
v___x_3832_ = lean_unsigned_to_nat(4u);
v___x_3833_ = lean_nat_mul(v_size_x27_3829_, v___x_3832_);
v___x_3834_ = lean_unsigned_to_nat(3u);
v___x_3835_ = lean_nat_div(v___x_3833_, v___x_3834_);
lean_dec(v___x_3833_);
v___x_3836_ = lean_array_get_size(v_buckets_x27_3831_);
v___x_3837_ = lean_nat_dec_le(v___x_3835_, v___x_3836_);
lean_dec(v___x_3835_);
if (v___x_3837_ == 0)
{
lean_object* v_val_3838_; lean_object* v___x_3840_; 
v_val_3838_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__2_spec__4___redArg(v_buckets_x27_3831_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 1, v_val_3838_);
lean_ctor_set(v___x_3811_, 0, v_size_x27_3829_);
v___x_3840_ = v___x_3811_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_size_x27_3829_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_val_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
else
{
lean_object* v___x_3843_; 
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 1, v_buckets_x27_3831_);
lean_ctor_set(v___x_3811_, 0, v_size_x27_3829_);
v___x_3843_ = v___x_3811_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_size_x27_3829_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v_buckets_x27_3831_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
else
{
lean_object* v___x_3845_; lean_object* v_buckets_x27_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3850_; 
lean_inc(v_bkt_3826_);
v___x_3845_ = lean_box(0);
v_buckets_x27_3846_ = lean_array_uset(v_buckets_3809_, v___x_3825_, v___x_3845_);
v___x_3847_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_3806_, v_b_3807_, v_bkt_3826_);
v___x_3848_ = lean_array_uset(v_buckets_x27_3846_, v___x_3825_, v___x_3847_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 1, v___x_3848_);
v___x_3850_ = v___x_3811_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_size_3808_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(lean_object* v_as_3853_, size_t v_sz_3854_, size_t v_i_3855_, lean_object* v_b_3856_){
_start:
{
uint8_t v___x_3858_; 
v___x_3858_ = lean_usize_dec_lt(v_i_3855_, v_sz_3854_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; 
v___x_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3859_, 0, v_b_3856_);
return v___x_3859_;
}
else
{
lean_object* v_snd_3860_; lean_object* v_fst_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3896_; 
v_snd_3860_ = lean_ctor_get(v_b_3856_, 1);
v_fst_3861_ = lean_ctor_get(v_b_3856_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v_b_3856_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3863_ = v_b_3856_;
v_isShared_3864_ = v_isSharedCheck_3896_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_snd_3860_);
lean_inc(v_fst_3861_);
lean_dec(v_b_3856_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3896_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v_array_3865_; lean_object* v_start_3866_; lean_object* v_stop_3867_; uint8_t v___x_3868_; 
v_array_3865_ = lean_ctor_get(v_snd_3860_, 0);
v_start_3866_ = lean_ctor_get(v_snd_3860_, 1);
v_stop_3867_ = lean_ctor_get(v_snd_3860_, 2);
v___x_3868_ = lean_nat_dec_lt(v_start_3866_, v_stop_3867_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3870_; 
if (v_isShared_3864_ == 0)
{
v___x_3870_ = v___x_3863_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_fst_3861_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_snd_3860_);
v___x_3870_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
return v___x_3871_;
}
}
else
{
lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3892_; 
lean_inc(v_stop_3867_);
lean_inc(v_start_3866_);
lean_inc_ref(v_array_3865_);
v_isSharedCheck_3892_ = !lean_is_exclusive(v_snd_3860_);
if (v_isSharedCheck_3892_ == 0)
{
lean_object* v_unused_3893_; lean_object* v_unused_3894_; lean_object* v_unused_3895_; 
v_unused_3893_ = lean_ctor_get(v_snd_3860_, 2);
lean_dec(v_unused_3893_);
v_unused_3894_ = lean_ctor_get(v_snd_3860_, 1);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_snd_3860_, 0);
lean_dec(v_unused_3895_);
v___x_3874_ = v_snd_3860_;
v_isShared_3875_ = v_isSharedCheck_3892_;
goto v_resetjp_3873_;
}
else
{
lean_dec(v_snd_3860_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3892_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v_a_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3881_; 
v_a_3876_ = lean_array_uget_borrowed(v_as_3853_, v_i_3855_);
v___x_3877_ = lean_array_fget(v_array_3865_, v_start_3866_);
v___x_3878_ = lean_unsigned_to_nat(1u);
v___x_3879_ = lean_nat_add(v_start_3866_, v___x_3878_);
lean_dec(v_start_3866_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 1, v___x_3879_);
v___x_3881_ = v___x_3874_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_array_3865_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v___x_3879_);
lean_ctor_set(v_reuseFailAlloc_3891_, 2, v_stop_3867_);
v___x_3881_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
lean_object* v___x_3882_; lean_object* v___x_3884_; 
v___x_3882_ = l_Lean_LocalDecl_fvarId(v_a_3876_);
lean_inc(v_a_3876_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 1, v___x_3877_);
lean_ctor_set(v___x_3863_, 0, v_a_3876_);
v___x_3884_ = v___x_3863_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3876_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v___x_3877_);
v___x_3884_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; size_t v___x_3887_; size_t v___x_3888_; 
v___x_3885_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(v_fst_3861_, v___x_3882_, v___x_3884_);
v___x_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
lean_ctor_set(v___x_3886_, 1, v___x_3881_);
v___x_3887_ = ((size_t)1ULL);
v___x_3888_ = lean_usize_add(v_i_3855_, v___x_3887_);
v_i_3855_ = v___x_3888_;
v_b_3856_ = v___x_3886_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg___boxed(lean_object* v_as_3897_, lean_object* v_sz_3898_, lean_object* v_i_3899_, lean_object* v_b_3900_, lean_object* v___y_3901_){
_start:
{
size_t v_sz_boxed_3902_; size_t v_i_boxed_3903_; lean_object* v_res_3904_; 
v_sz_boxed_3902_ = lean_unbox_usize(v_sz_3898_);
lean_dec(v_sz_3898_);
v_i_boxed_3903_ = lean_unbox_usize(v_i_3899_);
lean_dec(v_i_3899_);
v_res_3904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_3897_, v_sz_boxed_3902_, v_i_boxed_3903_, v_b_3900_);
lean_dec_ref(v_as_3897_);
return v_res_3904_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__1));
v___x_3908_ = lean_unsigned_to_nat(2u);
v___x_3909_ = lean_unsigned_to_nat(366u);
v___x_3910_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3911_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3912_ = l_mkPanicMessageWithDecl(v___x_3911_, v___x_3910_, v___x_3909_, v___x_3908_, v___x_3907_);
return v___x_3912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4(void){
_start:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3914_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__3));
v___x_3915_ = lean_unsigned_to_nat(2u);
v___x_3916_ = lean_unsigned_to_nat(367u);
v___x_3917_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__0));
v___x_3918_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_3919_ = l_mkPanicMessageWithDecl(v___x_3918_, v___x_3917_, v___x_3916_, v___x_3915_, v___x_3914_);
return v___x_3919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3920_ = lean_box(0);
v___x_3921_ = lean_unsigned_to_nat(16u);
v___x_3922_ = lean_mk_array(v___x_3921_, v___x_3920_);
return v___x_3922_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6(void){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3923_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__5);
v___x_3924_ = lean_unsigned_to_nat(0u);
v___x_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
lean_ctor_set(v___x_3925_, 1, v___x_3923_);
return v___x_3925_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8(void){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3927_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__7));
v___x_3928_ = l_Lean_stringToMessageData(v___x_3927_);
return v___x_3928_;
}
}
static lean_object* _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10(void){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3930_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__9));
v___x_3931_ = l_Lean_stringToMessageData(v___x_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(lean_object* v_sortedDecls_3932_, lean_object* v_sortedArgs_3933_, lean_object* v_toSortDecls_3934_, lean_object* v_toSortArgs_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v___y_3940_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v_snd_3963_; lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3965_ = lean_array_get_size(v_sortedDecls_3932_);
v___x_3966_ = lean_array_get_size(v_sortedArgs_3933_);
v___x_3967_ = lean_nat_dec_eq(v___x_3965_, v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
lean_dec_ref(v_toSortArgs_3935_);
lean_dec_ref(v_sortedArgs_3933_);
lean_dec_ref(v_sortedDecls_3932_);
v___x_3968_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__2);
v___x_3969_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v___x_3968_, v_a_3936_, v_a_3937_);
return v___x_3969_;
}
else
{
lean_object* v___x_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; 
v___x_3970_ = lean_array_get_size(v_toSortDecls_3934_);
v___x_3971_ = lean_array_get_size(v_toSortArgs_3935_);
v___x_3972_ = lean_nat_dec_eq(v___x_3970_, v___x_3971_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_dec_ref(v_toSortArgs_3935_);
lean_dec_ref(v_sortedArgs_3933_);
lean_dec_ref(v_sortedDecls_3932_);
v___x_3973_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__4);
v___x_3974_ = l_panic___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__1(v___x_3973_, v_a_3936_, v_a_3937_);
return v___x_3974_;
}
else
{
lean_object* v___x_3975_; uint8_t v___x_3976_; 
v___x_3975_ = lean_unsigned_to_nat(0u);
v___x_3976_ = lean_nat_dec_eq(v___x_3970_, v___x_3975_);
if (v___x_3976_ == 0)
{
lean_object* v_toCold_3977_; lean_object* v_options_3978_; lean_object* v_inheritedTraceOptions_3979_; uint8_t v_hasTrace_3980_; lean_object* v___x_3981_; lean_object* v_cls_3982_; lean_object* v___y_3984_; lean_object* v___y_3985_; 
v_toCold_3977_ = lean_ctor_get(v_a_3936_, 0);
v_options_3978_ = lean_ctor_get(v_toCold_3977_, 2);
v_inheritedTraceOptions_3979_ = lean_ctor_get(v_toCold_3977_, 11);
v_hasTrace_3980_ = lean_ctor_get_uint8(v_options_3978_, sizeof(void*)*1);
v___x_3981_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v_cls_3982_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
if (v_hasTrace_3980_ == 0)
{
v___y_3984_ = v_a_3936_;
v___y_3985_ = v_a_3937_;
goto v___jp_3983_;
}
else
{
lean_object* v___x_4086_; uint8_t v___x_4087_; 
v___x_4086_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4087_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3979_, v_options_3978_, v___x_4086_);
if (v___x_4087_ == 0)
{
v___y_3984_ = v_a_3936_;
v___y_3985_ = v_a_3937_;
goto v___jp_3983_;
}
else
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__10);
v___x_4089_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__6(v_cls_3982_, v___x_4088_, v_a_3936_, v_a_3937_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_dec_ref_known(v___x_4089_, 1);
v___y_3984_ = v_a_3936_;
v___y_3985_ = v_a_3937_;
goto v___jp_3983_;
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_dec_ref(v_toSortArgs_3935_);
lean_dec_ref(v_sortedArgs_3933_);
lean_dec_ref(v_sortedDecls_3932_);
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4089_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4089_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
}
v___jp_3983_:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; size_t v_sz_3989_; size_t v___x_3990_; lean_object* v___x_3991_; 
v___x_3986_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__6);
v___x_3987_ = l_Array_toSubarray___redArg(v_sortedArgs_3933_, v___x_3975_, v___x_3966_);
v___x_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3986_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
v_sz_3989_ = lean_array_size(v_sortedDecls_3932_);
v___x_3990_ = ((size_t)0ULL);
v___x_3991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_sortedDecls_3932_, v_sz_3989_, v___x_3990_, v___x_3988_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_a_3992_; lean_object* v_fst_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4076_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_a_3992_);
lean_dec_ref_known(v___x_3991_, 1);
v_fst_3993_ = lean_ctor_get(v_a_3992_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v_a_3992_);
if (v_isSharedCheck_4076_ == 0)
{
lean_object* v_unused_4077_; 
v_unused_4077_ = lean_ctor_get(v_a_3992_, 1);
lean_dec(v_unused_4077_);
v___x_3995_ = v_a_3992_;
v_isShared_3996_ = v_isSharedCheck_4076_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_fst_3993_);
lean_dec(v_a_3992_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4076_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3997_; lean_object* v___x_3999_; 
v___x_3997_ = l_Array_toSubarray___redArg(v_toSortArgs_3935_, v___x_3975_, v___x_3971_);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 1, v___x_3997_);
v___x_3999_ = v___x_3995_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_fst_3993_);
lean_ctor_set(v_reuseFailAlloc_4075_, 1, v___x_3997_);
v___x_3999_ = v_reuseFailAlloc_4075_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
size_t v_sz_4000_; lean_object* v___x_4001_; 
v_sz_4000_ = lean_array_size(v_toSortDecls_3934_);
v___x_4001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_toSortDecls_3934_, v_sz_4000_, v___x_3990_, v___x_3999_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v_fst_4003_; lean_object* v_size_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref_known(v___x_4001_, 1);
v_fst_4003_ = lean_ctor_get(v_a_4002_, 0);
lean_inc_n(v_fst_4003_, 2);
lean_dec(v_a_4002_);
v_size_4004_ = lean_ctor_get(v_fst_4003_, 0);
v___x_4005_ = lean_mk_empty_array_with_capacity(v_size_4004_);
lean_inc_ref(v___x_4005_);
v___x_4006_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4006_, 0, v___x_3981_);
lean_ctor_set(v___x_4006_, 1, v___x_3981_);
lean_ctor_set(v___x_4006_, 2, v___x_4005_);
lean_ctor_set(v___x_4006_, 3, v___x_4005_);
v___x_4007_ = lean_box(0);
v___x_4008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_4003_, v_sortedDecls_3932_, v_sz_3989_, v___x_3990_, v___x_4007_, v___x_4006_, v___y_3984_, v___y_3985_);
lean_dec_ref(v_sortedDecls_3932_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v_snd_4010_; lean_object* v___x_4011_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v_snd_4010_ = lean_ctor_get(v_a_4009_, 1);
lean_inc(v_snd_4010_);
lean_dec(v_a_4009_);
v___x_4011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__3(v_fst_4003_, v_toSortDecls_3934_, v_sz_4000_, v___x_3990_, v___x_4007_, v_snd_4010_, v___y_3984_, v___y_3985_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v_snd_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4049_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v___x_4011_, 1);
v_snd_4013_ = lean_ctor_get(v_a_4012_, 1);
v_isSharedCheck_4049_ = !lean_is_exclusive(v_a_4012_);
if (v_isSharedCheck_4049_ == 0)
{
lean_object* v_unused_4050_; 
v_unused_4050_ = lean_ctor_get(v_a_4012_, 0);
lean_dec(v_unused_4050_);
v___x_4015_ = v_a_4012_;
v_isShared_4016_ = v_isSharedCheck_4049_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_snd_4013_);
lean_dec(v_a_4012_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4049_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v_toCold_4017_; lean_object* v_options_4018_; lean_object* v_newDecls_4019_; lean_object* v_newArgs_4020_; lean_object* v_inheritedTraceOptions_4021_; uint8_t v_hasTrace_4022_; lean_object* v___f_4023_; 
v_toCold_4017_ = lean_ctor_get(v___y_3984_, 0);
v_options_4018_ = lean_ctor_get(v_toCold_4017_, 2);
v_newDecls_4019_ = lean_ctor_get(v_snd_4013_, 2);
v_newArgs_4020_ = lean_ctor_get(v_snd_4013_, 3);
v_inheritedTraceOptions_4021_ = lean_ctor_get(v_toCold_4017_, 11);
v_hasTrace_4022_ = lean_ctor_get_uint8(v_options_4018_, sizeof(void*)*1);
lean_inc_ref(v_newArgs_4020_);
lean_inc_ref(v_newDecls_4019_);
v___f_4023_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4023_, 0, v_newDecls_4019_);
lean_closure_set(v___f_4023_, 1, v_newArgs_4020_);
if (v_hasTrace_4022_ == 0)
{
lean_del_object(v___x_4015_);
v___y_3959_ = v___f_4023_;
v___y_3960_ = v___x_4007_;
v___y_3961_ = v___y_3984_;
v___y_3962_ = v___y_3985_;
v_snd_3963_ = v_snd_4013_;
goto v___jp_3958_;
}
else
{
lean_object* v___x_4024_; uint8_t v___x_4025_; 
v___x_4024_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__13);
v___x_4025_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4021_, v_options_4018_, v___x_4024_);
if (v___x_4025_ == 0)
{
lean_del_object(v___x_4015_);
v___y_3959_ = v___f_4023_;
v___y_3960_ = v___x_4007_;
v___y_3961_ = v___y_3984_;
v___y_3962_ = v___y_3985_;
v_snd_3963_ = v_snd_4013_;
goto v___jp_3958_;
}
else
{
lean_object* v___x_4026_; size_t v_sz_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4034_; 
lean_inc_ref(v_newArgs_4020_);
lean_inc_ref_n(v_newDecls_4019_, 2);
lean_dec_ref(v___f_4023_);
v___x_4026_ = lean_obj_once(&l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8, &l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8_once, _init_l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___closed__8);
v_sz_4027_ = lean_array_size(v_newDecls_4019_);
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__4(v_sz_4027_, v___x_3990_, v_newDecls_4019_);
v___x_4029_ = lean_array_to_list(v___x_4028_);
v___x_4030_ = lean_box(0);
v___x_4031_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__5(v___x_4029_, v___x_4030_);
v___x_4032_ = l_Lean_MessageData_ofList(v___x_4031_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set_tag(v___x_4015_, 7);
lean_ctor_set(v___x_4015_, 1, v___x_4032_);
lean_ctor_set(v___x_4015_, 0, v___x_4026_);
v___x_4034_ = v___x_4015_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4026_);
lean_ctor_set(v_reuseFailAlloc_4048_, 1, v___x_4032_);
v___x_4034_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_object* v___x_4035_; 
v___x_4035_ = l_Lean_addTrace___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit_spec__6(v_cls_3982_, v___x_4034_, v_snd_4013_, v___y_3984_, v___y_3985_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v_fst_4037_; lean_object* v_snd_4038_; lean_object* v___x_4039_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
lean_dec_ref_known(v___x_4035_, 1);
v_fst_4037_ = lean_ctor_get(v_a_4036_, 0);
lean_inc(v_fst_4037_);
v_snd_4038_ = lean_ctor_get(v_a_4036_, 1);
lean_inc(v_snd_4038_);
lean_dec(v_a_4036_);
v___x_4039_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___lam__0(v_newDecls_4019_, v_newArgs_4020_, v_fst_4037_, v_snd_4038_, v___y_3984_, v___y_3985_);
v___y_3940_ = v___x_4039_;
goto v___jp_3939_;
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
lean_dec_ref(v_newArgs_4020_);
lean_dec_ref(v_newDecls_4019_);
v_a_4040_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_4035_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4035_);
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
}
}
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
v_a_4051_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4011_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4011_);
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
lean_dec(v_fst_4003_);
v_a_4059_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4008_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4008_);
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
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
lean_dec_ref(v_sortedDecls_3932_);
v_a_4067_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4001_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4001_);
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
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_dec_ref(v_toSortArgs_3935_);
lean_dec_ref(v_sortedDecls_3932_);
v_a_4078_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_3991_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_3991_);
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
else
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
lean_dec_ref(v_toSortArgs_3935_);
v___x_4098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4098_, 0, v_sortedDecls_3932_);
lean_ctor_set(v___x_4098_, 1, v_sortedArgs_3933_);
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
return v___x_4099_;
}
}
}
v___jp_3939_:
{
if (lean_obj_tag(v___y_3940_) == 0)
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3949_; 
v_a_3941_ = lean_ctor_get(v___y_3940_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___y_3940_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3943_ = v___y_3940_;
v_isShared_3944_ = v_isSharedCheck_3949_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___y_3940_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3949_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v_fst_3945_; lean_object* v___x_3947_; 
v_fst_3945_ = lean_ctor_get(v_a_3941_, 0);
lean_inc(v_fst_3945_);
lean_dec(v_a_3941_);
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 0, v_fst_3945_);
v___x_3947_ = v___x_3943_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_fst_3945_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
else
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3957_; 
v_a_3950_ = lean_ctor_get(v___y_3940_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___y_3940_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3952_ = v___y_3940_;
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___y_3940_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3950_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
v___jp_3958_:
{
lean_object* v___x_3964_; 
lean_inc(v___y_3962_);
lean_inc_ref(v___y_3961_);
v___x_3964_ = lean_apply_5(v___y_3959_, v___y_3960_, v_snd_3963_, v___y_3961_, v___y_3962_, lean_box(0));
v___y_3940_ = v___x_3964_;
goto v___jp_3939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls___boxed(lean_object* v_sortedDecls_4100_, lean_object* v_sortedArgs_4101_, lean_object* v_toSortDecls_4102_, lean_object* v_toSortArgs_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v_sortedDecls_4100_, v_sortedArgs_4101_, v_toSortDecls_4102_, v_toSortArgs_4103_, v_a_4104_, v_a_4105_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
lean_dec_ref(v_toSortDecls_4102_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0(lean_object* v_00_u03b2_4108_, lean_object* v_m_4109_, lean_object* v_a_4110_, lean_object* v_b_4111_){
_start:
{
lean_object* v___x_4112_; 
v___x_4112_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0___redArg(v_m_4109_, v_a_4110_, v_b_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(lean_object* v_as_4113_, size_t v_sz_4114_, size_t v_i_4115_, lean_object* v_b_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___redArg(v_as_4113_, v_sz_4114_, v_i_4115_, v_b_4116_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2___boxed(lean_object* v_as_4121_, lean_object* v_sz_4122_, lean_object* v_i_4123_, lean_object* v_b_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
size_t v_sz_boxed_4128_; size_t v_i_boxed_4129_; lean_object* v_res_4130_; 
v_sz_boxed_4128_ = lean_unbox_usize(v_sz_4122_);
lean_dec(v_sz_4122_);
v_i_boxed_4129_ = lean_unbox_usize(v_i_4123_);
lean_dec(v_i_4123_);
v_res_4130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__2(v_as_4121_, v_sz_boxed_4128_, v_i_boxed_4129_, v_b_4124_, v___y_4125_, v___y_4126_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec_ref(v_as_4121_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0(lean_object* v_00_u03b2_4131_, lean_object* v_a_4132_, lean_object* v_b_4133_, lean_object* v_x_4134_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_spec__0_spec__0___redArg(v_a_4132_, v_b_4133_, v_x_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(lean_object* v_msg_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v___f_4143_; lean_object* v___x_1240__overap_4144_; lean_object* v___x_4145_; 
v___f_4143_ = ((lean_object*)(l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___closed__0));
v___x_1240__overap_4144_ = lean_panic_fn_borrowed(v___f_4143_, v_msg_4137_);
lean_inc(v___y_4141_);
lean_inc_ref(v___y_4140_);
lean_inc(v___y_4139_);
lean_inc_ref(v___y_4138_);
v___x_4145_ = lean_apply_5(v___x_1240__overap_4144_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, lean_box(0));
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0___boxed(lean_object* v_msg_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v_msg_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
return v_res_4152_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0(void){
_start:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4153_ = lean_box(0);
v___x_4154_ = lean_unsigned_to_nat(16u);
v___x_4155_ = lean_mk_array(v___x_4154_, v___x_4153_);
return v___x_4155_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1(void){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4156_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__0, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__0_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__0);
v___x_4157_ = lean_unsigned_to_nat(0u);
v___x_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
lean_ctor_set(v___x_4158_, 1, v___x_4156_);
return v___x_4158_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3(void){
_start:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4161_ = lean_unsigned_to_nat(1u);
v___x_4162_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__2));
v___x_4163_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__1, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__1_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__1);
v___x_4164_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
lean_ctor_set(v___x_4164_, 2, v___x_4162_);
lean_ctor_set(v___x_4164_, 3, v___x_4161_);
lean_ctor_set(v___x_4164_, 4, v___x_4162_);
lean_ctor_set(v___x_4164_, 5, v___x_4162_);
lean_ctor_set(v___x_4164_, 6, v___x_4162_);
lean_ctor_set(v___x_4164_, 7, v___x_4162_);
lean_ctor_set(v___x_4164_, 8, v___x_4161_);
lean_ctor_set(v___x_4164_, 9, v___x_4162_);
lean_ctor_set(v___x_4164_, 10, v___x_4162_);
lean_ctor_set(v___x_4164_, 11, v___x_4162_);
return v___x_4164_;
}
}
static lean_object* _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6(void){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4167_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__5));
v___x_4168_ = lean_unsigned_to_nat(2u);
v___x_4169_ = lean_unsigned_to_nat(417u);
v___x_4170_ = ((lean_object*)(l_Lean_Meta_Closure_mkValueTypeClosure___closed__4));
v___x_4171_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__2));
v___x_4172_ = l_mkPanicMessageWithDecl(v___x_4171_, v___x_4170_, v___x_4169_, v___x_4168_, v___x_4167_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object* v_type_4173_, lean_object* v_value_4174_, uint8_t v_zetaDelta_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4181_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__3, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__3_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__3);
v___x_4182_ = lean_st_mk_ref(v___x_4181_);
v___x_4183_ = l_Lean_Meta_Closure_mkValueTypeClosureAux(v_type_4173_, v_value_4174_, v_zetaDelta_4175_, v___x_4182_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4185_; lean_object* v_fst_4186_; lean_object* v_snd_4187_; lean_object* v_levelParams_4188_; lean_object* v_levelArgs_4189_; lean_object* v_newLocalDecls_4190_; lean_object* v_newLocalDeclsForMVars_4191_; lean_object* v_newLetDecls_4192_; lean_object* v_exprMVarArgs_4193_; lean_object* v_exprFVarArgs_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4183_, 1);
v___x_4185_ = lean_st_ref_get(v___x_4182_);
lean_dec(v___x_4182_);
v_fst_4186_ = lean_ctor_get(v_a_4184_, 0);
lean_inc(v_fst_4186_);
v_snd_4187_ = lean_ctor_get(v_a_4184_, 1);
lean_inc(v_snd_4187_);
lean_dec(v_a_4184_);
v_levelParams_4188_ = lean_ctor_get(v___x_4185_, 2);
lean_inc_ref(v_levelParams_4188_);
v_levelArgs_4189_ = lean_ctor_get(v___x_4185_, 4);
lean_inc_ref(v_levelArgs_4189_);
v_newLocalDecls_4190_ = lean_ctor_get(v___x_4185_, 5);
lean_inc_ref(v_newLocalDecls_4190_);
v_newLocalDeclsForMVars_4191_ = lean_ctor_get(v___x_4185_, 6);
lean_inc_ref(v_newLocalDeclsForMVars_4191_);
v_newLetDecls_4192_ = lean_ctor_get(v___x_4185_, 7);
lean_inc_ref(v_newLetDecls_4192_);
v_exprMVarArgs_4193_ = lean_ctor_get(v___x_4185_, 9);
lean_inc_ref(v_exprMVarArgs_4193_);
v_exprFVarArgs_4194_ = lean_ctor_get(v___x_4185_, 10);
lean_inc_ref(v_exprFVarArgs_4194_);
lean_dec(v___x_4185_);
v___x_4195_ = l_Array_reverse___redArg(v_newLocalDecls_4190_);
v___x_4196_ = l_Array_reverse___redArg(v_exprFVarArgs_4194_);
v___x_4197_ = l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls(v___x_4195_, v___x_4196_, v_newLocalDeclsForMVars_4191_, v_exprMVarArgs_4193_, v_a_4178_, v_a_4179_);
lean_dec_ref(v_newLocalDeclsForMVars_4191_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4216_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4200_ = v___x_4197_;
v_isShared_4201_ = v_isSharedCheck_4216_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4197_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4216_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v_fst_4202_; lean_object* v_snd_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; uint8_t v___x_4209_; 
v_fst_4202_ = lean_ctor_get(v_a_4198_, 0);
lean_inc_n(v_fst_4202_, 2);
v_snd_4203_ = lean_ctor_get(v_a_4198_, 1);
lean_inc(v_snd_4203_);
lean_dec(v_a_4198_);
v___x_4204_ = l_Array_reverse___redArg(v_newLetDecls_4192_);
lean_inc_ref(v___x_4204_);
v___x_4205_ = l_Lean_Meta_Closure_mkForall(v___x_4204_, v_fst_4186_);
lean_dec(v_fst_4186_);
v___x_4206_ = l_Lean_Meta_Closure_mkForall(v_fst_4202_, v___x_4205_);
lean_dec_ref(v___x_4205_);
v___x_4207_ = l_Lean_Meta_Closure_mkLambda(v___x_4204_, v_snd_4187_);
lean_dec(v_snd_4187_);
v___x_4208_ = l_Lean_Meta_Closure_mkLambda(v_fst_4202_, v___x_4207_);
lean_dec_ref(v___x_4207_);
v___x_4209_ = l_Lean_Expr_hasFVar(v___x_4208_);
if (v___x_4209_ == 0)
{
lean_object* v___x_4210_; lean_object* v___x_4212_; 
v___x_4210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4210_, 0, v_levelParams_4188_);
lean_ctor_set(v___x_4210_, 1, v___x_4206_);
lean_ctor_set(v___x_4210_, 2, v___x_4208_);
lean_ctor_set(v___x_4210_, 3, v_levelArgs_4189_);
lean_ctor_set(v___x_4210_, 4, v_snd_4203_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 0, v___x_4210_);
v___x_4212_ = v___x_4200_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
else
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
lean_dec_ref(v___x_4208_);
lean_dec_ref(v___x_4206_);
lean_dec(v_snd_4203_);
lean_del_object(v___x_4200_);
lean_dec_ref(v_levelArgs_4189_);
lean_dec_ref(v_levelParams_4188_);
v___x_4214_ = lean_obj_once(&l_Lean_Meta_Closure_mkValueTypeClosure___closed__6, &l_Lean_Meta_Closure_mkValueTypeClosure___closed__6_once, _init_l_Lean_Meta_Closure_mkValueTypeClosure___closed__6);
v___x_4215_ = l_panic___at___00Lean_Meta_Closure_mkValueTypeClosure_spec__0(v___x_4214_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
return v___x_4215_;
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec_ref(v_newLetDecls_4192_);
lean_dec_ref(v_levelArgs_4189_);
lean_dec_ref(v_levelParams_4188_);
lean_dec(v_snd_4187_);
lean_dec(v_fst_4186_);
v_a_4217_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4197_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4197_);
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
else
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
lean_dec(v___x_4182_);
v_a_4225_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4183_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4183_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Closure_mkValueTypeClosure___boxed(lean_object* v_type_4233_, lean_object* v_value_4234_, lean_object* v_zetaDelta_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_){
_start:
{
uint8_t v_zetaDelta_boxed_4241_; lean_object* v_res_4242_; 
v_zetaDelta_boxed_4241_ = lean_unbox(v_zetaDelta_4235_);
v_res_4242_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4233_, v_value_4234_, v_zetaDelta_boxed_4241_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
lean_dec(v_a_4239_);
lean_dec_ref(v_a_4238_);
lean_dec(v_a_4237_);
lean_dec_ref(v_a_4236_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(lean_object* v_name_4243_, lean_object* v_levelParams_4244_, lean_object* v_type_4245_, lean_object* v_value_4246_, lean_object* v_hints_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; uint8_t v___y_4252_; uint8_t v___y_4259_; lean_object* v_env_4262_; uint8_t v___x_4263_; 
v___x_4250_ = lean_st_ref_get(v___y_4248_);
v_env_4262_ = lean_ctor_get(v___x_4250_, 0);
lean_inc_ref_n(v_env_4262_, 2);
lean_dec(v___x_4250_);
v___x_4263_ = l_Lean_Environment_hasUnsafe(v_env_4262_, v_type_4245_);
if (v___x_4263_ == 0)
{
uint8_t v___x_4264_; 
v___x_4264_ = l_Lean_Environment_hasUnsafe(v_env_4262_, v_value_4246_);
v___y_4259_ = v___x_4264_;
goto v___jp_4258_;
}
else
{
lean_dec_ref(v_env_4262_);
v___y_4259_ = v___x_4263_;
goto v___jp_4258_;
}
v___jp_4251_:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
lean_inc(v_name_4243_);
v___x_4253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4253_, 0, v_name_4243_);
lean_ctor_set(v___x_4253_, 1, v_levelParams_4244_);
lean_ctor_set(v___x_4253_, 2, v_type_4245_);
v___x_4254_ = lean_box(0);
v___x_4255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4255_, 0, v_name_4243_);
lean_ctor_set(v___x_4255_, 1, v___x_4254_);
v___x_4256_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4256_, 0, v___x_4253_);
lean_ctor_set(v___x_4256_, 1, v_value_4246_);
lean_ctor_set(v___x_4256_, 2, v_hints_4247_);
lean_ctor_set(v___x_4256_, 3, v___x_4255_);
lean_ctor_set_uint8(v___x_4256_, sizeof(void*)*4, v___y_4252_);
v___x_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4256_);
return v___x_4257_;
}
v___jp_4258_:
{
if (v___y_4259_ == 0)
{
uint8_t v___x_4260_; 
v___x_4260_ = 1;
v___y_4252_ = v___x_4260_;
goto v___jp_4251_;
}
else
{
uint8_t v___x_4261_; 
v___x_4261_ = 0;
v___y_4252_ = v___x_4261_;
goto v___jp_4251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg___boxed(lean_object* v_name_4265_, lean_object* v_levelParams_4266_, lean_object* v_type_4267_, lean_object* v_value_4268_, lean_object* v_hints_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4265_, v_levelParams_4266_, v_type_4267_, v_value_4268_, v_hints_4269_, v___y_4270_);
lean_dec(v___y_4270_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(lean_object* v_name_4273_, lean_object* v_levelParams_4274_, lean_object* v_type_4275_, lean_object* v_value_4276_, lean_object* v_hints_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4273_, v_levelParams_4274_, v_type_4275_, v_value_4276_, v_hints_4277_, v___y_4281_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___boxed(lean_object* v_name_4284_, lean_object* v_levelParams_4285_, lean_object* v_type_4286_, lean_object* v_value_4287_, lean_object* v_hints_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0(v_name_4284_, v_levelParams_4285_, v_type_4286_, v_value_4287_, v_hints_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition(lean_object* v_name_4295_, lean_object* v_type_4296_, lean_object* v_value_4297_, uint8_t v_zetaDelta_4298_, uint8_t v_compile_4299_, uint8_t v_logCompileErrors_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4296_, v_value_4297_, v_zetaDelta_4298_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4358_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4309_ = v___x_4306_;
v_isShared_4310_ = v_isSharedCheck_4358_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4306_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4358_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4320_; lean_object* v_env_4321_; lean_object* v_levelParams_4322_; lean_object* v_type_4323_; lean_object* v_value_4324_; uint32_t v___x_4325_; uint32_t v___x_4326_; uint32_t v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4357_; 
v___x_4320_ = lean_st_ref_get(v_a_4304_);
v_env_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc_ref(v_env_4321_);
lean_dec(v___x_4320_);
v_levelParams_4322_ = lean_ctor_get(v_a_4307_, 0);
v_type_4323_ = lean_ctor_get(v_a_4307_, 1);
v_value_4324_ = lean_ctor_get(v_a_4307_, 2);
lean_inc_ref_n(v_value_4324_, 2);
v___x_4325_ = l_Lean_getMaxHeight(v_env_4321_, v_value_4324_);
v___x_4326_ = 1;
v___x_4327_ = lean_uint32_add(v___x_4325_, v___x_4326_);
v___x_4328_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4328_, 0, v___x_4327_);
lean_inc_ref(v_levelParams_4322_);
v___x_4329_ = lean_array_to_list(v_levelParams_4322_);
lean_inc_ref(v_type_4323_);
lean_inc(v_name_4295_);
v___x_4330_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkAuxDefinition_spec__0___redArg(v_name_4295_, v___x_4329_, v_type_4323_, v_value_4324_, v___x_4328_, v_a_4304_);
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4333_ = v___x_4330_;
v_isShared_4334_ = v_isSharedCheck_4357_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4330_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4357_;
goto v_resetjp_4332_;
}
v___jp_4311_:
{
lean_object* v_levelArgs_4312_; lean_object* v_exprArgs_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4318_; 
v_levelArgs_4312_ = lean_ctor_get(v_a_4307_, 3);
lean_inc_ref(v_levelArgs_4312_);
v_exprArgs_4313_ = lean_ctor_get(v_a_4307_, 4);
lean_inc_ref(v_exprArgs_4313_);
lean_dec(v_a_4307_);
v___x_4314_ = lean_array_to_list(v_levelArgs_4312_);
v___x_4315_ = l_Lean_mkConst(v_name_4295_, v___x_4314_);
v___x_4316_ = l_Lean_mkAppN(v___x_4315_, v_exprArgs_4313_);
lean_dec_ref(v_exprArgs_4313_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 0, v___x_4316_);
v___x_4318_ = v___x_4309_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4316_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
lean_ctor_set_tag(v___x_4333_, 1);
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
uint8_t v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = 0;
lean_inc_ref(v___x_4336_);
v___x_4338_ = l_Lean_addDecl(v___x_4336_, v___x_4337_, v_a_4303_, v_a_4304_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_dec_ref_known(v___x_4338_, 1);
if (v_compile_4299_ == 0)
{
lean_dec_ref(v___x_4336_);
goto v___jp_4311_;
}
else
{
lean_object* v___x_4339_; 
v___x_4339_ = l_Lean_compileDecl(v___x_4336_, v_logCompileErrors_4300_, v_a_4303_, v_a_4304_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_dec_ref_known(v___x_4339_, 1);
goto v___jp_4311_;
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
lean_del_object(v___x_4309_);
lean_dec(v_a_4307_);
lean_dec(v_name_4295_);
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4339_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4339_);
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
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
lean_dec_ref(v___x_4336_);
lean_del_object(v___x_4309_);
lean_dec(v_a_4307_);
lean_dec(v_name_4295_);
v_a_4348_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4338_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4338_);
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
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
lean_dec(v_name_4295_);
v_a_4359_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4306_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4306_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinition___boxed(lean_object* v_name_4367_, lean_object* v_type_4368_, lean_object* v_value_4369_, lean_object* v_zetaDelta_4370_, lean_object* v_compile_4371_, lean_object* v_logCompileErrors_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_){
_start:
{
uint8_t v_zetaDelta_boxed_4378_; uint8_t v_compile_boxed_4379_; uint8_t v_logCompileErrors_boxed_4380_; lean_object* v_res_4381_; 
v_zetaDelta_boxed_4378_ = lean_unbox(v_zetaDelta_4370_);
v_compile_boxed_4379_ = lean_unbox(v_compile_4371_);
v_logCompileErrors_boxed_4380_ = lean_unbox(v_logCompileErrors_4372_);
v_res_4381_ = l_Lean_Meta_mkAuxDefinition(v_name_4367_, v_type_4368_, v_value_4369_, v_zetaDelta_boxed_4378_, v_compile_boxed_4379_, v_logCompileErrors_boxed_4380_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
lean_dec(v_a_4376_);
lean_dec_ref(v_a_4375_);
lean_dec(v_a_4374_);
lean_dec_ref(v_a_4373_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object* v_name_4382_, lean_object* v_value_4383_, uint8_t v_zetaDelta_4384_, uint8_t v_compile_4385_, uint8_t v_logCompileErrors_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v___x_4392_; 
lean_inc(v_a_4390_);
lean_inc_ref(v_a_4389_);
lean_inc(v_a_4388_);
lean_inc_ref(v_a_4387_);
lean_inc_ref(v_value_4383_);
v___x_4392_ = lean_infer_type(v_value_4383_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_a_4393_);
lean_dec_ref_known(v___x_4392_, 1);
v___x_4394_ = l_Lean_Expr_headBeta(v_a_4393_);
v___x_4395_ = l_Lean_Meta_mkAuxDefinition(v_name_4382_, v___x_4394_, v_value_4383_, v_zetaDelta_4384_, v_compile_4385_, v_logCompileErrors_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
return v___x_4395_;
}
else
{
lean_dec_ref(v_value_4383_);
lean_dec(v_name_4382_);
return v___x_4392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxDefinitionFor___boxed(lean_object* v_name_4396_, lean_object* v_value_4397_, lean_object* v_zetaDelta_4398_, lean_object* v_compile_4399_, lean_object* v_logCompileErrors_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_){
_start:
{
uint8_t v_zetaDelta_boxed_4406_; uint8_t v_compile_boxed_4407_; uint8_t v_logCompileErrors_boxed_4408_; lean_object* v_res_4409_; 
v_zetaDelta_boxed_4406_ = lean_unbox(v_zetaDelta_4398_);
v_compile_boxed_4407_ = lean_unbox(v_compile_4399_);
v_logCompileErrors_boxed_4408_ = lean_unbox(v_logCompileErrors_4400_);
v_res_4409_ = l_Lean_Meta_mkAuxDefinitionFor(v_name_4396_, v_value_4397_, v_zetaDelta_boxed_4406_, v_compile_boxed_4407_, v_logCompileErrors_boxed_4408_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_);
lean_dec(v_a_4404_);
lean_dec_ref(v_a_4403_);
lean_dec(v_a_4402_);
lean_dec_ref(v_a_4401_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem(lean_object* v_type_4410_, lean_object* v_value_4411_, uint8_t v_zetaDelta_4412_, lean_object* v_kind_x3f_4413_, uint8_t v_cache_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_){
_start:
{
lean_object* v___x_4420_; 
v___x_4420_ = l_Lean_Meta_Closure_mkValueTypeClosure(v_type_4410_, v_value_4411_, v_zetaDelta_4412_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v_levelParams_4422_; lean_object* v_type_4423_; lean_object* v_value_4424_; lean_object* v_levelArgs_4425_; lean_object* v_exprArgs_4426_; lean_object* v___x_4427_; uint8_t v___x_4428_; lean_object* v___x_4429_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4420_, 1);
v_levelParams_4422_ = lean_ctor_get(v_a_4421_, 0);
lean_inc_ref(v_levelParams_4422_);
v_type_4423_ = lean_ctor_get(v_a_4421_, 1);
lean_inc_ref(v_type_4423_);
v_value_4424_ = lean_ctor_get(v_a_4421_, 2);
lean_inc_ref(v_value_4424_);
v_levelArgs_4425_ = lean_ctor_get(v_a_4421_, 3);
lean_inc_ref(v_levelArgs_4425_);
v_exprArgs_4426_ = lean_ctor_get(v_a_4421_, 4);
lean_inc_ref(v_exprArgs_4426_);
lean_dec(v_a_4421_);
v___x_4427_ = lean_array_to_list(v_levelParams_4422_);
v___x_4428_ = 0;
v___x_4429_ = l_Lean_Meta_mkAuxLemma(v___x_4427_, v_type_4423_, v_value_4424_, v_kind_x3f_4413_, v_cache_4414_, v___x_4428_, v___x_4428_, v___x_4428_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4440_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4432_ = v___x_4429_;
v_isShared_4433_ = v_isSharedCheck_4440_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4429_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4440_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4438_; 
v___x_4434_ = lean_array_to_list(v_levelArgs_4425_);
v___x_4435_ = l_Lean_mkConst(v_a_4430_, v___x_4434_);
v___x_4436_ = l_Lean_mkAppN(v___x_4435_, v_exprArgs_4426_);
lean_dec_ref(v_exprArgs_4426_);
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 0, v___x_4436_);
v___x_4438_ = v___x_4432_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec_ref(v_exprArgs_4426_);
lean_dec_ref(v_levelArgs_4425_);
v_a_4441_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4429_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4429_);
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
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_dec(v_kind_x3f_4413_);
v_a_4449_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4420_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4420_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object* v_type_4457_, lean_object* v_value_4458_, lean_object* v_zetaDelta_4459_, lean_object* v_kind_x3f_4460_, lean_object* v_cache_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_){
_start:
{
uint8_t v_zetaDelta_boxed_4467_; uint8_t v_cache_boxed_4468_; lean_object* v_res_4469_; 
v_zetaDelta_boxed_4467_ = lean_unbox(v_zetaDelta_4459_);
v_cache_boxed_4468_ = lean_unbox(v_cache_4461_);
v_res_4469_ = l_Lean_Meta_mkAuxTheorem(v_type_4457_, v_value_4458_, v_zetaDelta_boxed_4467_, v_kind_x3f_4460_, v_cache_boxed_4468_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_);
lean_dec(v_a_4465_);
lean_dec_ref(v_a_4464_);
lean_dec(v_a_4463_);
lean_dec_ref(v_a_4462_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4525_; uint8_t v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4525_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_Closure_sortDecls_visit___closed__10));
v___x_4526_ = 0;
v___x_4527_ = ((lean_object*)(l___private_Lean_Meta_Closure_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_));
v___x_4528_ = l_Lean_registerTraceClass(v___x_4525_, v___x_4526_, v___x_4527_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2____boxed(lean_object* v_a_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l___private_Lean_Meta_Closure_0__Lean_Meta_initFn_00___x40_Lean_Meta_Closure_210311863____hygCtx___hyg_2_();
return v_res_4530_;
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
