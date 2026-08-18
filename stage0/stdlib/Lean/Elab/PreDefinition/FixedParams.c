// Lean compiler output
// Module: Lean.Elab.PreDefinition.FixedParams
// Imports: public import Lean.Elab.PreDefinition.Basic import Init.Omega
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Std_Format_indentD(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_init(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_addSelfCalls(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0;
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParams_Info_mayBeFixed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_mayBeFixed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParams_Info_setVarying___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setVarying(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setVarying___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_getCallerParam_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setCallerParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setCallerParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_FixedParams_Info_format_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__1_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__2 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__2_value;
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__2_value)}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__3 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "❌"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__1_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2_value;
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2_value)}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__3 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__3_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__4 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__4_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__5 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__5_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__6;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7;
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__4_value)}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__8 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__8_value;
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__5_value)}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "• "};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_format(lean_object*);
static const lean_closure_object l_Lean_Elab_FixedParams_instToFormatInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_FixedParams_Info_format, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_FixedParams_instToFormatInfo___closed__0 = (const lean_object*)&l_Lean_Elab_FixedParams_instToFormatInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_FixedParams_instToFormatInfo = (const lean_object*)&l_Lean_Elab_FixedParams_instToFormatInfo___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_getParamRevDeps___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_getParamRevDeps___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_getParamRevDeps___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_getParamRevDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_getParamRevDeps___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_getParamRevDeps___closed__0 = (const lean_object*)&l_Lean_Elab_getParamRevDeps___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fixedParams"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(80, 131, 105, 217, 25, 82, 145, 102)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "getFixedParams: notFixed "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ":\nIn "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "\ntoo few arguments for "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =/= "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " not matched"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Elab.PreDefinition.FixedParams"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Elab.getFixedParamsInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 185, .m_capacity = 185, .m_length = 184, .m_data = "assertion violation: params.size = arities[callerIdx]!\n\n      -- TODO: transform is overkill, a simple visit-all-subexpression that takes applications\n      -- as whole suffices\n      "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_getFixedParamsInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "getFixedParams:"};
static const lean_object* l_Lean_Elab_getFixedParamsInfo___closed__0 = (const lean_object*)&l_Lean_Elab_getFixedParamsInfo___closed__0_value;
static lean_once_cell_t l_Lean_Elab_getFixedParamsInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getFixedParamsInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__0_value),((lean_object*)&l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__0_value)}};
static const lean_object* l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1 = (const lean_object*)&l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedFixedParamPerms_default = (const lean_object*)&l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedFixedParamPerms = (const lean_object*)&l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1_value;
static const lean_string_object l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1_value;
static const lean_string_object l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__2 = (const lean_object*)&l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3 = (const lean_object*)&l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3_value;
static lean_once_cell_t l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5;
static const lean_ctor_object l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6_value;
static const lean_string_object l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "numFixed"};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7;
static const lean_string_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "perms"};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10;
static const lean_string_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "revDeps"};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13;
static const lean_string_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15;
static lean_once_cell_t l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16;
static const lean_ctor_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instReprFixedParamPerms___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instReprFixedParamPerms_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instReprFixedParamPerms___closed__0 = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instReprFixedParamPerms = (const lean_object*)&l_Lean_Elab_instReprFixedParamPerms___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Elab.getFixedParamPerms"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "assertion violation: paramInfo[0]! = some paramIdx\n        "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "assertion violation: firstPerm[firstParamIdx]!.isSome\n            "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Incomplete paramInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_getFixedParamPerms___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: xs.size = paramInfos.size\n\n    "};
static const lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_getFixedParamPerms___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "_private.Lean.Elab.PreDefinition.FixedParams.0.Lean.Elab.FixedParamPerm.forallTelescopeImpl.go"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: type.isForall\n      "};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "assertion violation: xs'.size = 1\n        "};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: fixedParamIdx < xs.size\n        "};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "assertion violation: !( __do_lift._@.Lean.Elab.PreDefinition.FixedParams.75993854._hygCtx._hyg.102.0 ).hasLooseBVars\n        "};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "_private.Lean.Elab.PreDefinition.FixedParams.0.Lean.Elab.FixedParamPerm.instantiateForall.go"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "assertion violation: ys.size = 1\n          "};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Elab.FixedParamPerm.instantiateForall"};
static const lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0 = (const lean_object*)&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0_value;
static const lean_string_object l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "assertion violation: xs.size = perm.numFixed\n  "};
static const lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1 = (const lean_object*)&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1_value;
static lean_once_cell_t l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "_private.Lean.Elab.PreDefinition.FixedParams.0.Lean.Elab.FixedParamPerm.instantiateLambda.go"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "assertion violation: ys.size = 1\n            "};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Elab.FixedParamPerm.instantiateLambda"};
static const lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0 = (const lean_object*)&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0_value;
static lean_once_cell_t l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "_private.Lean.Elab.PreDefinition.FixedParams.0.Lean.Elab.FixedParamPerm.pickFixed.go"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: fixedParamIdx < ys.size\n        "};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Elab.FixedParamPerm.pickFixed"};
static const lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "assertion violation: xs.size = perm.size\n  "};
static const lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2;
static const lean_array_object l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "_private.Lean.Elab.PreDefinition.FixedParams.0.Lean.Elab.FixedParamPerm.buildArgs.go"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "FixedParams.buildArgs: too few varying args"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "FixedParams.buildArgs: too few fixed args"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Elab.FixedParamPerm.buildArgs"};
static const lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: fixedArgs.size = perm.numFixed\n  "};
static const lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.FixedParamPerms.erase"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "assertion violation: paramIdx < mapping.size\n      "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_FixedParamPerms_erase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "assertion violation: fixedParamPerms.numFixed  = xs.size\n  "};
static const lean_object* l_Lean_Elab_FixedParamPerms_erase___closed__0 = (const lean_object*)&l_Lean_Elab_FixedParamPerms_erase___closed__0_value;
static lean_once_cell_t l_Lean_Elab_FixedParamPerms_erase___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParamPerms_erase___closed__1;
static const lean_string_object l_Lean_Elab_FixedParamPerms_erase___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 134, .m_capacity = 134, .m_length = 133, .m_data = "assertion violation: toErase.size = fixedParamPerms.perms.size\n  -- Calculate a mask on the fixed parameters of variables to erase\n  "};
static const lean_object* l_Lean_Elab_FixedParamPerms_erase___closed__2 = (const lean_object*)&l_Lean_Elab_FixedParamPerms_erase___closed__2_value;
static lean_once_cell_t l_Lean_Elab_FixedParamPerms_erase___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParamPerms_erase___closed__3;
static const lean_string_object l_Lean_Elab_FixedParamPerms_erase___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 41, .m_data = "assertion violation: xs.all (·.isFVar)\n  "};
static const lean_object* l_Lean_Elab_FixedParamPerms_erase___closed__4 = (const lean_object*)&l_Lean_Elab_FixedParamPerms_erase___closed__4_value;
static lean_once_cell_t l_Lean_Elab_FixedParamPerms_erase___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParamPerms_erase___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "FixedParams"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 87, 32, 251, 113, 133, 158, 252)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(140, 135, 17, 208, 62, 57, 192, 16)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(249, 225, 135, 56, 213, 49, 154, 134)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 208, 124, 62, 167, 39, 159, 30)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 118, 73, 0, 78, 121, 48, 169)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 144, 90, 0, 164, 70, 155, 205)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(80, 80, 200, 145, 119, 202, 92, 1)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 27, 9, 206, 200, 16, 168, 251)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)(((size_t)(791000795) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(47, 149, 235, 94, 82, 130, 210, 117)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 33, 115, 184, 239, 184, 190, 148)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(48, 81, 13, 137, 134, 8, 99, 98)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(225, 58, 56, 207, 96, 242, 57, 49)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0(lean_object* v_revDeps_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_bs_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_lt(v_i_3_, v_sz_2_);
if (v___x_5_ == 0)
{
return v_bs_4_;
}
else
{
lean_object* v_v_6_; lean_object* v___x_7_; lean_object* v_bs_x27_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; size_t v___x_15_; size_t v___x_16_; lean_object* v___x_17_; 
v_v_6_ = lean_array_uget(v_bs_4_, v_i_3_);
v___x_7_ = lean_unsigned_to_nat(0u);
v_bs_x27_8_ = lean_array_uset(v_bs_4_, v_i_3_, v___x_7_);
v___x_9_ = lean_array_get_size(v_v_6_);
lean_dec(v_v_6_);
v___x_10_ = lean_array_get_size(v_revDeps_1_);
v___x_11_ = lean_box(0);
v___x_12_ = lean_mk_array(v___x_10_, v___x_11_);
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
v___x_14_ = lean_mk_array(v___x_9_, v___x_13_);
v___x_15_ = ((size_t)1ULL);
v___x_16_ = lean_usize_add(v_i_3_, v___x_15_);
v___x_17_ = lean_array_uset(v_bs_x27_8_, v_i_3_, v___x_14_);
v_i_3_ = v___x_16_;
v_bs_4_ = v___x_17_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0___boxed(lean_object* v_revDeps_19_, lean_object* v_sz_20_, lean_object* v_i_21_, lean_object* v_bs_22_){
_start:
{
size_t v_sz_boxed_23_; size_t v_i_boxed_24_; lean_object* v_res_25_; 
v_sz_boxed_23_ = lean_unbox_usize(v_sz_20_);
lean_dec(v_sz_20_);
v_i_boxed_24_ = lean_unbox_usize(v_i_21_);
lean_dec(v_i_21_);
v_res_25_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0(v_revDeps_19_, v_sz_boxed_23_, v_i_boxed_24_, v_bs_22_);
lean_dec_ref(v_revDeps_19_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_init(lean_object* v_revDeps_26_){
_start:
{
size_t v_sz_27_; size_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_sz_27_ = lean_array_size(v_revDeps_26_);
v___x_28_ = ((size_t)0ULL);
lean_inc_ref(v_revDeps_26_);
v___x_29_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0(v_revDeps_26_, v_sz_27_, v___x_28_, v_revDeps_26_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v_revDeps_26_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(lean_object* v_i_31_, size_t v_sz_32_, size_t v_i_33_, lean_object* v_bs_34_){
_start:
{
uint8_t v___x_35_; 
v___x_35_ = lean_usize_dec_lt(v_i_33_, v_sz_32_);
if (v___x_35_ == 0)
{
return v_bs_34_;
}
else
{
lean_object* v_v_36_; lean_object* v___x_37_; lean_object* v_bs_x27_38_; lean_object* v___y_40_; 
v_v_36_ = lean_array_uget(v_bs_34_, v_i_33_);
v___x_37_ = lean_unsigned_to_nat(0u);
v_bs_x27_38_ = lean_array_uset(v_bs_34_, v_i_33_, v___x_37_);
if (lean_obj_tag(v_v_36_) == 0)
{
v___y_40_ = v_v_36_;
goto v___jp_39_;
}
else
{
lean_object* v_val_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_55_; 
v_val_45_ = lean_ctor_get(v_v_36_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v_v_36_);
if (v_isSharedCheck_55_ == 0)
{
v___x_47_ = v_v_36_;
v_isShared_48_ = v_isSharedCheck_55_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_val_45_);
lean_dec(v_v_36_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_55_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_51_; 
v___x_49_ = lean_usize_to_nat(v_i_33_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v___x_49_);
v___x_51_ = v___x_47_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_49_);
v___x_51_ = v_reuseFailAlloc_54_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_array_set(v_val_45_, v_i_31_, v___x_51_);
v___x_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
v___y_40_ = v___x_53_;
goto v___jp_39_;
}
}
}
v___jp_39_:
{
size_t v___x_41_; size_t v___x_42_; lean_object* v___x_43_; 
v___x_41_ = ((size_t)1ULL);
v___x_42_ = lean_usize_add(v_i_33_, v___x_41_);
v___x_43_ = lean_array_uset(v_bs_x27_38_, v_i_33_, v___y_40_);
v_i_33_ = v___x_42_;
v_bs_34_ = v___x_43_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg___boxed(lean_object* v_i_56_, lean_object* v_sz_57_, lean_object* v_i_58_, lean_object* v_bs_59_){
_start:
{
size_t v_sz_boxed_60_; size_t v_i_boxed_61_; lean_object* v_res_62_; 
v_sz_boxed_60_ = lean_unbox_usize(v_sz_57_);
lean_dec(v_sz_57_);
v_i_boxed_61_ = lean_unbox_usize(v_i_58_);
lean_dec(v_i_58_);
v_res_62_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(v_i_56_, v_sz_boxed_60_, v_i_boxed_61_, v_bs_59_);
lean_dec(v_i_56_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(size_t v_sz_63_, size_t v_i_64_, lean_object* v_bs_65_){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = lean_usize_dec_lt(v_i_64_, v_sz_63_);
if (v___x_66_ == 0)
{
return v_bs_65_;
}
else
{
lean_object* v_v_67_; lean_object* v___x_68_; lean_object* v_bs_x27_69_; lean_object* v___x_70_; size_t v_sz_71_; size_t v___x_72_; lean_object* v___x_73_; size_t v___x_74_; size_t v___x_75_; lean_object* v___x_76_; 
v_v_67_ = lean_array_uget(v_bs_65_, v_i_64_);
v___x_68_ = lean_unsigned_to_nat(0u);
v_bs_x27_69_ = lean_array_uset(v_bs_65_, v_i_64_, v___x_68_);
v___x_70_ = lean_usize_to_nat(v_i_64_);
v_sz_71_ = lean_array_size(v_v_67_);
v___x_72_ = ((size_t)0ULL);
v___x_73_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(v___x_70_, v_sz_71_, v___x_72_, v_v_67_);
lean_dec(v___x_70_);
v___x_74_ = ((size_t)1ULL);
v___x_75_ = lean_usize_add(v_i_64_, v___x_74_);
v___x_76_ = lean_array_uset(v_bs_x27_69_, v_i_64_, v___x_73_);
v_i_64_ = v___x_75_;
v_bs_65_ = v___x_76_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg___boxed(lean_object* v_sz_78_, lean_object* v_i_79_, lean_object* v_bs_80_){
_start:
{
size_t v_sz_boxed_81_; size_t v_i_boxed_82_; lean_object* v_res_83_; 
v_sz_boxed_81_ = lean_unbox_usize(v_sz_78_);
lean_dec(v_sz_78_);
v_i_boxed_82_ = lean_unbox_usize(v_i_79_);
lean_dec(v_i_79_);
v_res_83_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(v_sz_boxed_81_, v_i_boxed_82_, v_bs_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_addSelfCalls(lean_object* v_info_84_){
_start:
{
lean_object* v_graph_85_; lean_object* v_revDeps_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_96_; 
v_graph_85_ = lean_ctor_get(v_info_84_, 0);
v_revDeps_86_ = lean_ctor_get(v_info_84_, 1);
v_isSharedCheck_96_ = !lean_is_exclusive(v_info_84_);
if (v_isSharedCheck_96_ == 0)
{
v___x_88_ = v_info_84_;
v_isShared_89_ = v_isSharedCheck_96_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_revDeps_86_);
lean_inc(v_graph_85_);
lean_dec(v_info_84_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_96_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
size_t v_sz_90_; size_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v_sz_90_ = lean_array_size(v_graph_85_);
v___x_91_ = ((size_t)0ULL);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(v_sz_90_, v___x_91_, v_graph_85_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_92_);
v___x_94_ = v___x_88_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_revDeps_86_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0(lean_object* v_i_97_, lean_object* v_as_98_, size_t v_sz_99_, size_t v_i_100_, lean_object* v_bs_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(v_i_97_, v_sz_99_, v_i_100_, v_bs_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___boxed(lean_object* v_i_103_, lean_object* v_as_104_, lean_object* v_sz_105_, lean_object* v_i_106_, lean_object* v_bs_107_){
_start:
{
size_t v_sz_boxed_108_; size_t v_i_boxed_109_; lean_object* v_res_110_; 
v_sz_boxed_108_ = lean_unbox_usize(v_sz_105_);
lean_dec(v_sz_105_);
v_i_boxed_109_ = lean_unbox_usize(v_i_106_);
lean_dec(v_i_106_);
v_res_110_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0(v_i_103_, v_as_104_, v_sz_boxed_108_, v_i_boxed_109_, v_bs_107_);
lean_dec_ref(v_as_104_);
lean_dec(v_i_103_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1(lean_object* v_as_111_, size_t v_sz_112_, size_t v_i_113_, lean_object* v_bs_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(v_sz_112_, v_i_113_, v_bs_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___boxed(lean_object* v_as_116_, lean_object* v_sz_117_, lean_object* v_i_118_, lean_object* v_bs_119_){
_start:
{
size_t v_sz_boxed_120_; size_t v_i_boxed_121_; lean_object* v_res_122_; 
v_sz_boxed_120_ = lean_unbox_usize(v_sz_117_);
lean_dec(v_sz_117_);
v_i_boxed_121_ = lean_unbox_usize(v_i_118_);
lean_dec(v_i_118_);
v_res_122_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1(v_as_116_, v_sz_boxed_120_, v_i_boxed_121_, v_bs_119_);
lean_dec_ref(v_as_116_);
return v_res_122_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Array_instInhabited(lean_box(0));
return v___x_123_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParams_Info_mayBeFixed(lean_object* v_callerIdx_124_, lean_object* v_paramIdx_125_, lean_object* v_info_126_){
_start:
{
lean_object* v_graph_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_graph_127_ = lean_ctor_get(v_info_126_, 0);
v___x_128_ = lean_box(0);
v___x_129_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_130_ = lean_array_get_borrowed(v___x_129_, v_graph_127_, v_callerIdx_124_);
v___x_131_ = lean_array_get_borrowed(v___x_128_, v___x_130_, v_paramIdx_125_);
if (lean_obj_tag(v___x_131_) == 0)
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 1;
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_mayBeFixed___boxed(lean_object* v_callerIdx_134_, lean_object* v_paramIdx_135_, lean_object* v_info_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_callerIdx_134_, v_paramIdx_135_, v_info_136_);
lean_dec_ref(v_info_136_);
lean_dec(v_paramIdx_135_);
lean_dec(v_callerIdx_134_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(lean_object* v_upperBound_139_, lean_object* v_next_140_, lean_object* v_funIdx_141_, lean_object* v_paramIdx_142_, lean_object* v_a_143_, lean_object* v_b_144_){
_start:
{
lean_object* v_a_146_; uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_lt(v_a_143_, v_upperBound_139_);
if (v___x_150_ == 0)
{
lean_dec(v_a_143_);
lean_dec(v_paramIdx_142_);
return v_b_144_;
}
else
{
lean_object* v_graph_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_graph_151_ = lean_ctor_get(v_b_144_, 0);
v___x_152_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_153_ = lean_box(0);
v___x_154_ = lean_array_get_borrowed(v___x_152_, v_graph_151_, v_next_140_);
v___x_155_ = lean_array_get(v___x_153_, v___x_154_, v_a_143_);
if (lean_obj_tag(v___x_155_) == 1)
{
lean_object* v_val_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_167_; 
v_val_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_167_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_167_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_val_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_167_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_160_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_161_ = lean_array_get(v___x_153_, v_val_156_, v_funIdx_141_);
lean_dec(v_val_156_);
lean_inc(v_paramIdx_142_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v_paramIdx_142_);
v___x_163_ = v___x_158_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_paramIdx_142_);
v___x_163_ = v_reuseFailAlloc_166_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
uint8_t v___x_164_; 
v___x_164_ = l_Option_instDecidableEq___redArg(v___x_160_, v___x_161_, v___x_163_);
if (v___x_164_ == 0)
{
v_a_146_ = v_b_144_;
goto v___jp_145_;
}
else
{
lean_object* v___x_165_; 
lean_inc(v_a_143_);
v___x_165_ = l_Lean_Elab_FixedParams_Info_setVarying(v_next_140_, v_a_143_, v_b_144_);
v_a_146_ = v___x_165_;
goto v___jp_145_;
}
}
}
}
else
{
lean_dec(v___x_155_);
v_a_146_ = v_b_144_;
goto v___jp_145_;
}
}
v___jp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(1u);
v___x_148_ = lean_nat_add(v_a_143_, v___x_147_);
lean_dec(v_a_143_);
v_a_143_ = v___x_148_;
v_b_144_ = v_a_146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(lean_object* v_upperBound_168_, lean_object* v_funIdx_169_, lean_object* v_paramIdx_170_, lean_object* v_a_171_, lean_object* v_b_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = lean_nat_dec_lt(v_a_171_, v_upperBound_168_);
if (v___x_173_ == 0)
{
lean_dec(v_a_171_);
lean_dec(v_paramIdx_170_);
return v_b_172_;
}
else
{
lean_object* v_graph_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_graph_174_ = lean_ctor_get(v_b_172_, 0);
v___x_175_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_176_ = lean_array_get_borrowed(v___x_175_, v_graph_174_, v_a_171_);
v___x_177_ = lean_array_get_size(v___x_176_);
v___x_178_ = lean_unsigned_to_nat(0u);
lean_inc(v_paramIdx_170_);
v___x_179_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(v___x_177_, v_a_171_, v_funIdx_169_, v_paramIdx_170_, v___x_178_, v_b_172_);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_a_171_, v___x_180_);
lean_dec(v_a_171_);
v_a_171_ = v___x_181_;
v_b_172_ = v___x_179_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0(void){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Array_instInhabited(lean_box(0));
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setVarying(lean_object* v_funIdx_184_, lean_object* v_paramIdx_185_, lean_object* v_info_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_funIdx_184_, v_paramIdx_185_, v_info_186_);
if (v___x_187_ == 0)
{
lean_dec(v_paramIdx_185_);
return v_info_186_;
}
else
{
lean_object* v_graph_188_; lean_object* v_revDeps_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_216_; 
v_graph_188_ = lean_ctor_get(v_info_186_, 0);
v_revDeps_189_ = lean_ctor_get(v_info_186_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_info_186_);
if (v_isSharedCheck_216_ == 0)
{
v___x_191_ = v_info_186_;
v_isShared_192_ = v_isSharedCheck_216_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_revDeps_189_);
lean_inc(v_graph_188_);
lean_dec(v_info_186_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_216_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___y_194_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_array_get_size(v_graph_188_);
v___x_209_ = lean_nat_dec_lt(v_funIdx_184_, v___x_208_);
if (v___x_209_ == 0)
{
v___y_194_ = v_graph_188_;
goto v___jp_193_;
}
else
{
lean_object* v_v_210_; lean_object* v___x_211_; lean_object* v_xs_x27_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_v_210_ = lean_array_fget(v_graph_188_, v_funIdx_184_);
v___x_211_ = lean_box(0);
v_xs_x27_212_ = lean_array_fset(v_graph_188_, v_funIdx_184_, v___x_211_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_array_set(v_v_210_, v_paramIdx_185_, v___x_213_);
v___x_215_ = lean_array_fset(v_xs_x27_212_, v_funIdx_184_, v___x_214_);
v___y_194_ = v___x_215_;
goto v___jp_193_;
}
v___jp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_info_198_; 
v___x_195_ = lean_array_get_size(v___y_194_);
v___x_196_ = lean_unsigned_to_nat(0u);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___y_194_);
v_info_198_ = v___x_191_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___y_194_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_revDeps_189_);
v_info_198_ = v_reuseFailAlloc_207_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v_revDeps_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; size_t v_sz_204_; size_t v___x_205_; lean_object* v___x_206_; 
lean_inc(v_paramIdx_185_);
v___x_199_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(v___x_195_, v_funIdx_184_, v_paramIdx_185_, v___x_196_, v_info_198_);
v_revDeps_200_ = lean_ctor_get(v___x_199_, 1);
lean_inc_ref(v_revDeps_200_);
v___x_201_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_202_ = lean_array_get(v___x_201_, v_revDeps_200_, v_funIdx_184_);
lean_dec_ref(v_revDeps_200_);
v___x_203_ = lean_array_get(v___x_201_, v___x_202_, v_paramIdx_185_);
lean_dec(v_paramIdx_185_);
lean_dec(v___x_202_);
v_sz_204_ = lean_array_size(v___x_203_);
v___x_205_ = ((size_t)0ULL);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(v_funIdx_184_, v___x_203_, v_sz_204_, v___x_205_, v___x_199_);
lean_dec(v___x_203_);
return v___x_206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(lean_object* v_funIdx_217_, lean_object* v_as_218_, size_t v_sz_219_, size_t v_i_220_, lean_object* v_b_221_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = lean_usize_dec_lt(v_i_220_, v_sz_219_);
if (v___x_222_ == 0)
{
return v_b_221_;
}
else
{
lean_object* v_a_223_; lean_object* v___x_224_; size_t v___x_225_; size_t v___x_226_; 
v_a_223_ = lean_array_uget_borrowed(v_as_218_, v_i_220_);
lean_inc(v_a_223_);
v___x_224_ = l_Lean_Elab_FixedParams_Info_setVarying(v_funIdx_217_, v_a_223_, v_b_221_);
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_add(v_i_220_, v___x_225_);
v_i_220_ = v___x_226_;
v_b_221_ = v___x_224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0___boxed(lean_object* v_funIdx_228_, lean_object* v_as_229_, lean_object* v_sz_230_, lean_object* v_i_231_, lean_object* v_b_232_){
_start:
{
size_t v_sz_boxed_233_; size_t v_i_boxed_234_; lean_object* v_res_235_; 
v_sz_boxed_233_ = lean_unbox_usize(v_sz_230_);
lean_dec(v_sz_230_);
v_i_boxed_234_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_res_235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(v_funIdx_228_, v_as_229_, v_sz_boxed_233_, v_i_boxed_234_, v_b_232_);
lean_dec_ref(v_as_229_);
lean_dec(v_funIdx_228_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg___boxed(lean_object* v_upperBound_236_, lean_object* v_funIdx_237_, lean_object* v_paramIdx_238_, lean_object* v_a_239_, lean_object* v_b_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(v_upperBound_236_, v_funIdx_237_, v_paramIdx_238_, v_a_239_, v_b_240_);
lean_dec(v_funIdx_237_);
lean_dec(v_upperBound_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg___boxed(lean_object* v_upperBound_242_, lean_object* v_next_243_, lean_object* v_funIdx_244_, lean_object* v_paramIdx_245_, lean_object* v_a_246_, lean_object* v_b_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(v_upperBound_242_, v_next_243_, v_funIdx_244_, v_paramIdx_245_, v_a_246_, v_b_247_);
lean_dec(v_funIdx_244_);
lean_dec(v_next_243_);
lean_dec(v_upperBound_242_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setVarying___boxed(lean_object* v_funIdx_249_, lean_object* v_paramIdx_250_, lean_object* v_info_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Elab_FixedParams_Info_setVarying(v_funIdx_249_, v_paramIdx_250_, v_info_251_);
lean_dec(v_funIdx_249_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1(lean_object* v_upperBound_253_, lean_object* v_next_254_, lean_object* v_funIdx_255_, lean_object* v_paramIdx_256_, lean_object* v_inst_257_, lean_object* v_R_258_, lean_object* v_a_259_, lean_object* v_b_260_, lean_object* v_c_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(v_upperBound_253_, v_next_254_, v_funIdx_255_, v_paramIdx_256_, v_a_259_, v_b_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___boxed(lean_object* v_upperBound_263_, lean_object* v_next_264_, lean_object* v_funIdx_265_, lean_object* v_paramIdx_266_, lean_object* v_inst_267_, lean_object* v_R_268_, lean_object* v_a_269_, lean_object* v_b_270_, lean_object* v_c_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1(v_upperBound_263_, v_next_264_, v_funIdx_265_, v_paramIdx_266_, v_inst_267_, v_R_268_, v_a_269_, v_b_270_, v_c_271_);
lean_dec(v_funIdx_265_);
lean_dec(v_next_264_);
lean_dec(v_upperBound_263_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2(lean_object* v_upperBound_273_, lean_object* v_funIdx_274_, lean_object* v_paramIdx_275_, lean_object* v_inst_276_, lean_object* v_R_277_, lean_object* v_a_278_, lean_object* v_b_279_, lean_object* v_c_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(v_upperBound_273_, v_funIdx_274_, v_paramIdx_275_, v_a_278_, v_b_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___boxed(lean_object* v_upperBound_282_, lean_object* v_funIdx_283_, lean_object* v_paramIdx_284_, lean_object* v_inst_285_, lean_object* v_R_286_, lean_object* v_a_287_, lean_object* v_b_288_, lean_object* v_c_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2(v_upperBound_282_, v_funIdx_283_, v_paramIdx_284_, v_inst_285_, v_R_286_, v_a_287_, v_b_288_, v_c_289_);
lean_dec(v_funIdx_283_);
lean_dec(v_upperBound_282_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(lean_object* v_calleeIdx_291_, lean_object* v_argIdx_292_, lean_object* v_callerIdx_293_, lean_object* v_info_294_){
_start:
{
lean_object* v_graph_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_graph_295_ = lean_ctor_get(v_info_294_, 0);
v___x_296_ = lean_box(0);
v___x_297_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_298_ = lean_array_get_borrowed(v___x_297_, v_graph_295_, v_calleeIdx_291_);
v___x_299_ = lean_array_get_borrowed(v___x_296_, v___x_298_, v_argIdx_292_);
if (lean_obj_tag(v___x_299_) == 0)
{
return v___x_296_;
}
else
{
lean_object* v_val_300_; lean_object* v___x_301_; 
v_val_300_ = lean_ctor_get(v___x_299_, 0);
v___x_301_ = lean_array_get_borrowed(v___x_296_, v_val_300_, v_callerIdx_293_);
lean_inc(v___x_301_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_getCallerParam_x3f___boxed(lean_object* v_calleeIdx_302_, lean_object* v_argIdx_303_, lean_object* v_callerIdx_304_, lean_object* v_info_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_calleeIdx_302_, v_argIdx_303_, v_callerIdx_304_, v_info_305_);
lean_dec_ref(v_info_305_);
lean_dec(v_callerIdx_304_);
lean_dec(v_argIdx_303_);
lean_dec(v_calleeIdx_302_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(lean_object* v_upperBound_307_, lean_object* v_val_308_, lean_object* v_calleeIdx_309_, lean_object* v_argIdx_310_, lean_object* v_a_311_, lean_object* v_b_312_){
_start:
{
lean_object* v_a_314_; uint8_t v___x_318_; 
v___x_318_ = lean_nat_dec_lt(v_a_311_, v_upperBound_307_);
if (v___x_318_ == 0)
{
lean_dec(v_a_311_);
lean_dec(v_argIdx_310_);
return v_b_312_;
}
else
{
lean_object* v___x_319_; 
v___x_319_ = lean_array_fget_borrowed(v_val_308_, v_a_311_);
if (lean_obj_tag(v___x_319_) == 1)
{
lean_object* v_val_320_; lean_object* v___x_321_; 
v_val_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_val_320_);
lean_inc(v_argIdx_310_);
v___x_321_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_calleeIdx_309_, v_argIdx_310_, v_a_311_, v_val_320_, v_b_312_);
v_a_314_ = v___x_321_;
goto v___jp_313_;
}
else
{
v_a_314_ = v_b_312_;
goto v___jp_313_;
}
}
v___jp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_add(v_a_311_, v___x_315_);
lean_dec(v_a_311_);
v_a_311_ = v___x_316_;
v_b_312_ = v_a_314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setCallerParam(lean_object* v_calleeIdx_322_, lean_object* v_argIdx_323_, lean_object* v_callerIdx_324_, lean_object* v_paramIdx_325_, lean_object* v_info_326_){
_start:
{
lean_object* v_info_328_; lean_object* v_graph_329_; uint8_t v___x_333_; 
v___x_333_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_calleeIdx_322_, v_argIdx_323_, v_info_326_);
if (v___x_333_ == 0)
{
lean_dec(v_paramIdx_325_);
lean_dec(v_argIdx_323_);
return v_info_326_;
}
else
{
uint8_t v___x_334_; 
v___x_334_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_callerIdx_324_, v_paramIdx_325_, v_info_326_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec(v_paramIdx_325_);
v___x_335_ = l_Lean_Elab_FixedParams_Info_setVarying(v_calleeIdx_322_, v_argIdx_323_, v_info_326_);
return v___x_335_;
}
else
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_calleeIdx_322_, v_argIdx_323_, v_callerIdx_324_, v_info_326_);
if (lean_obj_tag(v___x_336_) == 1)
{
lean_object* v_val_337_; uint8_t v___x_338_; 
v_val_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_val_337_);
lean_dec_ref_known(v___x_336_, 1);
v___x_338_ = lean_nat_dec_eq(v_paramIdx_325_, v_val_337_);
lean_dec(v_val_337_);
lean_dec(v_paramIdx_325_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Elab_FixedParams_Info_setVarying(v_calleeIdx_322_, v_argIdx_323_, v_info_326_);
return v___x_339_;
}
else
{
lean_dec(v_argIdx_323_);
return v_info_326_;
}
}
else
{
lean_object* v_graph_340_; lean_object* v_revDeps_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_384_; 
lean_dec(v___x_336_);
v_graph_340_ = lean_ctor_get(v_info_326_, 0);
v_revDeps_341_ = lean_ctor_get(v_info_326_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_info_326_);
if (v_isSharedCheck_384_ == 0)
{
v___x_343_ = v_info_326_;
v_isShared_344_ = v_isSharedCheck_384_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_revDeps_341_);
lean_inc(v_graph_340_);
lean_dec(v_info_326_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_384_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___y_346_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = lean_array_get_size(v_graph_340_);
v___x_360_ = lean_nat_dec_lt(v_calleeIdx_322_, v___x_359_);
if (v___x_360_ == 0)
{
v___y_346_ = v_graph_340_;
goto v___jp_345_;
}
else
{
lean_object* v_v_361_; lean_object* v___x_362_; lean_object* v_xs_x27_363_; lean_object* v___y_365_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_v_361_ = lean_array_fget(v_graph_340_, v_calleeIdx_322_);
v___x_362_ = lean_box(0);
v_xs_x27_363_ = lean_array_fset(v_graph_340_, v_calleeIdx_322_, v___x_362_);
v___x_367_ = lean_array_get_size(v_v_361_);
v___x_368_ = lean_nat_dec_lt(v_argIdx_323_, v___x_367_);
if (v___x_368_ == 0)
{
v___y_365_ = v_v_361_;
goto v___jp_364_;
}
else
{
lean_object* v_v_369_; lean_object* v_xs_x27_370_; lean_object* v___y_372_; 
v_v_369_ = lean_array_fget(v_v_361_, v_argIdx_323_);
v_xs_x27_370_ = lean_array_fset(v_v_361_, v_argIdx_323_, v___x_362_);
if (lean_obj_tag(v_v_369_) == 0)
{
v___y_372_ = v_v_369_;
goto v___jp_371_;
}
else
{
lean_object* v_val_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_383_; 
v_val_374_ = lean_ctor_get(v_v_369_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_v_369_);
if (v_isSharedCheck_383_ == 0)
{
v___x_376_ = v_v_369_;
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_val_374_);
lean_dec(v_v_369_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
lean_inc(v_paramIdx_325_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v_paramIdx_325_);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_paramIdx_325_);
v___x_379_ = v_reuseFailAlloc_382_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_array_set(v_val_374_, v_callerIdx_324_, v___x_379_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___y_372_ = v___x_381_;
goto v___jp_371_;
}
}
}
v___jp_371_:
{
lean_object* v___x_373_; 
v___x_373_ = lean_array_fset(v_xs_x27_370_, v_argIdx_323_, v___y_372_);
v___y_365_ = v___x_373_;
goto v___jp_364_;
}
}
v___jp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_array_fset(v_xs_x27_363_, v_calleeIdx_322_, v___y_365_);
v___y_346_ = v___x_366_;
goto v___jp_345_;
}
}
v___jp_345_:
{
lean_object* v_info_348_; 
lean_inc_ref(v___y_346_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___y_346_);
v_info_348_ = v___x_343_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___y_346_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_revDeps_341_);
v_info_348_ = v_reuseFailAlloc_358_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_349_ = lean_box(0);
v___x_350_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_351_ = lean_array_get_borrowed(v___x_350_, v___y_346_, v_callerIdx_324_);
v___x_352_ = lean_array_get_borrowed(v___x_349_, v___x_351_, v_paramIdx_325_);
if (lean_obj_tag(v___x_352_) == 1)
{
lean_object* v_val_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_graph_357_; 
lean_inc_ref(v___x_352_);
lean_dec_ref(v___y_346_);
v_val_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_val_353_);
lean_dec_ref_known(v___x_352_, 1);
v___x_354_ = lean_array_get_size(v_val_353_);
v___x_355_ = lean_unsigned_to_nat(0u);
lean_inc(v_argIdx_323_);
v___x_356_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(v___x_354_, v_val_353_, v_calleeIdx_322_, v_argIdx_323_, v___x_355_, v_info_348_);
lean_dec(v_val_353_);
v_graph_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc_ref(v_graph_357_);
v_info_328_ = v___x_356_;
v_graph_329_ = v_graph_357_;
goto v___jp_327_;
}
else
{
v_info_328_ = v_info_348_;
v_graph_329_ = v___y_346_;
goto v___jp_327_;
}
}
}
}
}
}
}
v___jp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = lean_array_get_size(v_graph_329_);
lean_dec_ref(v_graph_329_);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(v___x_330_, v_calleeIdx_322_, v_argIdx_323_, v_callerIdx_324_, v_paramIdx_325_, v___x_331_, v_info_328_);
lean_dec(v_argIdx_323_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(lean_object* v_upperBound_385_, lean_object* v_next_386_, lean_object* v_calleeIdx_387_, lean_object* v_argIdx_388_, lean_object* v_callerIdx_389_, lean_object* v_paramIdx_390_, lean_object* v_a_391_, lean_object* v_b_392_){
_start:
{
lean_object* v_a_394_; uint8_t v___x_398_; 
v___x_398_ = lean_nat_dec_lt(v_a_391_, v_upperBound_385_);
if (v___x_398_ == 0)
{
lean_dec(v_a_391_);
lean_dec(v_paramIdx_390_);
return v_b_392_;
}
else
{
lean_object* v_graph_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_graph_399_ = lean_ctor_get(v_b_392_, 0);
v___x_400_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_401_ = lean_box(0);
v___x_402_ = lean_array_get_borrowed(v___x_400_, v_graph_399_, v_next_386_);
v___x_403_ = lean_array_get_borrowed(v___x_401_, v___x_402_, v_a_391_);
if (lean_obj_tag(v___x_403_) == 1)
{
lean_object* v_val_404_; lean_object* v___x_405_; 
v_val_404_ = lean_ctor_get(v___x_403_, 0);
v___x_405_ = lean_array_get_borrowed(v___x_401_, v_val_404_, v_calleeIdx_387_);
if (lean_obj_tag(v___x_405_) == 1)
{
lean_object* v_val_406_; uint8_t v___x_407_; 
v_val_406_ = lean_ctor_get(v___x_405_, 0);
v___x_407_ = lean_nat_dec_eq(v_val_406_, v_argIdx_388_);
if (v___x_407_ == 0)
{
v_a_394_ = v_b_392_;
goto v___jp_393_;
}
else
{
lean_object* v___x_408_; 
lean_inc(v_paramIdx_390_);
lean_inc(v_a_391_);
v___x_408_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_next_386_, v_a_391_, v_callerIdx_389_, v_paramIdx_390_, v_b_392_);
v_a_394_ = v___x_408_;
goto v___jp_393_;
}
}
else
{
v_a_394_ = v_b_392_;
goto v___jp_393_;
}
}
else
{
v_a_394_ = v_b_392_;
goto v___jp_393_;
}
}
v___jp_393_:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = lean_nat_add(v_a_391_, v___x_395_);
lean_dec(v_a_391_);
v_a_391_ = v___x_396_;
v_b_392_ = v_a_394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(lean_object* v_upperBound_409_, lean_object* v_calleeIdx_410_, lean_object* v_argIdx_411_, lean_object* v_callerIdx_412_, lean_object* v_paramIdx_413_, lean_object* v_a_414_, lean_object* v_b_415_){
_start:
{
uint8_t v___x_416_; 
v___x_416_ = lean_nat_dec_lt(v_a_414_, v_upperBound_409_);
if (v___x_416_ == 0)
{
lean_dec(v_a_414_);
lean_dec(v_paramIdx_413_);
return v_b_415_;
}
else
{
lean_object* v_graph_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_graph_417_ = lean_ctor_get(v_b_415_, 0);
v___x_418_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_419_ = lean_array_get_borrowed(v___x_418_, v_graph_417_, v_a_414_);
v___x_420_ = lean_array_get_size(v___x_419_);
v___x_421_ = lean_unsigned_to_nat(0u);
lean_inc(v_paramIdx_413_);
v___x_422_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(v___x_420_, v_a_414_, v_calleeIdx_410_, v_argIdx_411_, v_callerIdx_412_, v_paramIdx_413_, v___x_421_, v_b_415_);
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = lean_nat_add(v_a_414_, v___x_423_);
lean_dec(v_a_414_);
v_a_414_ = v___x_424_;
v_b_415_ = v___x_422_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg___boxed(lean_object* v_upperBound_426_, lean_object* v_calleeIdx_427_, lean_object* v_argIdx_428_, lean_object* v_callerIdx_429_, lean_object* v_paramIdx_430_, lean_object* v_a_431_, lean_object* v_b_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(v_upperBound_426_, v_calleeIdx_427_, v_argIdx_428_, v_callerIdx_429_, v_paramIdx_430_, v_a_431_, v_b_432_);
lean_dec(v_callerIdx_429_);
lean_dec(v_argIdx_428_);
lean_dec(v_calleeIdx_427_);
lean_dec(v_upperBound_426_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg___boxed(lean_object* v_upperBound_434_, lean_object* v_val_435_, lean_object* v_calleeIdx_436_, lean_object* v_argIdx_437_, lean_object* v_a_438_, lean_object* v_b_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(v_upperBound_434_, v_val_435_, v_calleeIdx_436_, v_argIdx_437_, v_a_438_, v_b_439_);
lean_dec(v_calleeIdx_436_);
lean_dec_ref(v_val_435_);
lean_dec(v_upperBound_434_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg___boxed(lean_object* v_upperBound_441_, lean_object* v_next_442_, lean_object* v_calleeIdx_443_, lean_object* v_argIdx_444_, lean_object* v_callerIdx_445_, lean_object* v_paramIdx_446_, lean_object* v_a_447_, lean_object* v_b_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(v_upperBound_441_, v_next_442_, v_calleeIdx_443_, v_argIdx_444_, v_callerIdx_445_, v_paramIdx_446_, v_a_447_, v_b_448_);
lean_dec(v_callerIdx_445_);
lean_dec(v_argIdx_444_);
lean_dec(v_calleeIdx_443_);
lean_dec(v_next_442_);
lean_dec(v_upperBound_441_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setCallerParam___boxed(lean_object* v_calleeIdx_450_, lean_object* v_argIdx_451_, lean_object* v_callerIdx_452_, lean_object* v_paramIdx_453_, lean_object* v_info_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_calleeIdx_450_, v_argIdx_451_, v_callerIdx_452_, v_paramIdx_453_, v_info_454_);
lean_dec(v_callerIdx_452_);
lean_dec(v_calleeIdx_450_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0(lean_object* v_upperBound_456_, lean_object* v_next_457_, lean_object* v_calleeIdx_458_, lean_object* v_argIdx_459_, lean_object* v_callerIdx_460_, lean_object* v_paramIdx_461_, lean_object* v_inst_462_, lean_object* v_R_463_, lean_object* v_a_464_, lean_object* v_b_465_, lean_object* v_c_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(v_upperBound_456_, v_next_457_, v_calleeIdx_458_, v_argIdx_459_, v_callerIdx_460_, v_paramIdx_461_, v_a_464_, v_b_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___boxed(lean_object* v_upperBound_468_, lean_object* v_next_469_, lean_object* v_calleeIdx_470_, lean_object* v_argIdx_471_, lean_object* v_callerIdx_472_, lean_object* v_paramIdx_473_, lean_object* v_inst_474_, lean_object* v_R_475_, lean_object* v_a_476_, lean_object* v_b_477_, lean_object* v_c_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0(v_upperBound_468_, v_next_469_, v_calleeIdx_470_, v_argIdx_471_, v_callerIdx_472_, v_paramIdx_473_, v_inst_474_, v_R_475_, v_a_476_, v_b_477_, v_c_478_);
lean_dec(v_callerIdx_472_);
lean_dec(v_argIdx_471_);
lean_dec(v_calleeIdx_470_);
lean_dec(v_next_469_);
lean_dec(v_upperBound_468_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1(lean_object* v_upperBound_480_, lean_object* v_calleeIdx_481_, lean_object* v_argIdx_482_, lean_object* v_callerIdx_483_, lean_object* v_paramIdx_484_, lean_object* v_inst_485_, lean_object* v_R_486_, lean_object* v_a_487_, lean_object* v_b_488_, lean_object* v_c_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(v_upperBound_480_, v_calleeIdx_481_, v_argIdx_482_, v_callerIdx_483_, v_paramIdx_484_, v_a_487_, v_b_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___boxed(lean_object* v_upperBound_491_, lean_object* v_calleeIdx_492_, lean_object* v_argIdx_493_, lean_object* v_callerIdx_494_, lean_object* v_paramIdx_495_, lean_object* v_inst_496_, lean_object* v_R_497_, lean_object* v_a_498_, lean_object* v_b_499_, lean_object* v_c_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1(v_upperBound_491_, v_calleeIdx_492_, v_argIdx_493_, v_callerIdx_494_, v_paramIdx_495_, v_inst_496_, v_R_497_, v_a_498_, v_b_499_, v_c_500_);
lean_dec(v_callerIdx_494_);
lean_dec(v_argIdx_493_);
lean_dec(v_calleeIdx_492_);
lean_dec(v_upperBound_491_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2(lean_object* v_upperBound_502_, lean_object* v_val_503_, lean_object* v_calleeIdx_504_, lean_object* v_argIdx_505_, lean_object* v_inst_506_, lean_object* v_R_507_, lean_object* v_a_508_, lean_object* v_b_509_, lean_object* v_c_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(v_upperBound_502_, v_val_503_, v_calleeIdx_504_, v_argIdx_505_, v_a_508_, v_b_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___boxed(lean_object* v_upperBound_512_, lean_object* v_val_513_, lean_object* v_calleeIdx_514_, lean_object* v_argIdx_515_, lean_object* v_inst_516_, lean_object* v_R_517_, lean_object* v_a_518_, lean_object* v_b_519_, lean_object* v_c_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2(v_upperBound_512_, v_val_513_, v_calleeIdx_514_, v_argIdx_515_, v_inst_516_, v_R_517_, v_a_518_, v_b_519_, v_c_520_);
lean_dec(v_calleeIdx_514_);
lean_dec_ref(v_val_513_);
lean_dec(v_upperBound_512_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_FixedParams_Info_format_spec__2(lean_object* v_a_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = lean_nat_to_int(v_a_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1_spec__1(lean_object* v_x_524_, lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_dec(v_x_524_);
return v_x_525_;
}
else
{
lean_object* v_head_527_; lean_object* v_tail_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_537_; 
v_head_527_ = lean_ctor_get(v_x_526_, 0);
v_tail_528_ = lean_ctor_get(v_x_526_, 1);
v_isSharedCheck_537_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_537_ == 0)
{
v___x_530_ = v_x_526_;
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_tail_528_);
lean_inc(v_head_527_);
lean_dec(v_x_526_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
lean_inc(v_x_524_);
if (v_isShared_531_ == 0)
{
lean_ctor_set_tag(v___x_530_, 5);
lean_ctor_set(v___x_530_, 1, v_x_524_);
lean_ctor_set(v___x_530_, 0, v_x_525_);
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_x_525_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_x_524_);
v___x_533_ = v_reuseFailAlloc_536_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v_head_527_);
v_x_525_ = v___x_534_;
v_x_526_ = v_tail_528_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
lean_object* v___x_540_; 
lean_dec(v_x_539_);
v___x_540_ = lean_box(0);
return v___x_540_;
}
else
{
lean_object* v_tail_541_; 
v_tail_541_ = lean_ctor_get(v_x_538_, 1);
if (lean_obj_tag(v_tail_541_) == 0)
{
lean_object* v_head_542_; 
lean_dec(v_x_539_);
v_head_542_ = lean_ctor_get(v_x_538_, 0);
lean_inc(v_head_542_);
lean_dec_ref_known(v_x_538_, 2);
return v_head_542_;
}
else
{
lean_object* v_head_543_; lean_object* v___x_544_; 
lean_inc(v_tail_541_);
v_head_543_ = lean_ctor_get(v_x_538_, 0);
lean_inc(v_head_543_);
lean_dec_ref_known(v_x_538_, 2);
v___x_544_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1_spec__1(v_x_539_, v_head_543_, v_tail_541_);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0(lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
if (lean_obj_tag(v_a_551_) == 0)
{
lean_object* v___x_553_; 
v___x_553_ = l_List_reverse___redArg(v_a_552_);
return v___x_553_;
}
else
{
lean_object* v_head_554_; lean_object* v_tail_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_579_; 
v_head_554_ = lean_ctor_get(v_a_551_, 0);
v_tail_555_ = lean_ctor_get(v_a_551_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_a_551_);
if (v_isSharedCheck_579_ == 0)
{
v___x_557_ = v_a_551_;
v_isShared_558_ = v_isSharedCheck_579_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_tail_555_);
lean_inc(v_head_554_);
lean_dec(v_a_551_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_579_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___y_560_; 
if (lean_obj_tag(v_head_554_) == 0)
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__1));
v___y_560_ = v___x_565_;
goto v___jp_559_;
}
else
{
lean_object* v_val_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_578_; 
v_val_566_ = lean_ctor_get(v_head_554_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_head_554_);
if (v_isSharedCheck_578_ == 0)
{
v___x_568_ = v_head_554_;
v_isShared_569_ = v_isSharedCheck_578_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_val_566_);
lean_dec(v_head_554_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_578_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_570_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__3));
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_nat_add(v_val_566_, v___x_571_);
lean_dec(v_val_566_);
v___x_573_ = l_Nat_reprFast(v___x_572_);
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 3);
lean_ctor_set(v___x_568_, 0, v___x_573_);
v___x_575_ = v___x_568_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_577_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_570_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___y_560_ = v___x_576_;
goto v___jp_559_;
}
}
}
v___jp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v_a_552_);
lean_ctor_set(v___x_557_, 0, v___y_560_);
v___x_562_ = v___x_557_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___y_560_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_a_552_);
v___x_562_ = v_reuseFailAlloc_564_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
v_a_551_ = v_tail_555_;
v_a_552_ = v___x_562_;
goto _start;
}
}
}
}
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__6(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__4));
v___x_589_ = lean_string_length(v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__6, &l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__6_once, _init_l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__6);
v___x_591_ = lean_nat_to_int(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3(lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
if (lean_obj_tag(v_a_596_) == 0)
{
lean_object* v___x_598_; 
v___x_598_ = l_List_reverse___redArg(v_a_597_);
return v___x_598_;
}
else
{
lean_object* v_head_599_; lean_object* v_tail_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_625_; 
v_head_599_ = lean_ctor_get(v_a_596_, 0);
v_tail_600_ = lean_ctor_get(v_a_596_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_625_ == 0)
{
v___x_602_ = v_a_596_;
v_isShared_603_ = v_isSharedCheck_625_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_tail_600_);
lean_inc(v_head_599_);
lean_dec(v_a_596_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_625_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___y_605_; 
if (lean_obj_tag(v_head_599_) == 0)
{
lean_object* v___x_610_; 
v___x_610_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__1));
v___y_605_ = v___x_610_;
goto v___jp_604_;
}
else
{
lean_object* v_val_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; 
v_val_611_ = lean_ctor_get(v_head_599_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v_head_599_, 1);
v___x_612_ = lean_array_to_list(v_val_611_);
v___x_613_ = lean_box(0);
v___x_614_ = l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0(v___x_612_, v___x_613_);
v___x_615_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__3));
v___x_616_ = l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(v___x_614_, v___x_615_);
v___x_617_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7, &l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7_once, _init_l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7);
v___x_618_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__8));
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___x_616_);
v___x_620_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_617_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = 0;
v___x_624_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*1, v___x_623_);
v___y_605_ = v___x_624_;
goto v___jp_604_;
}
v___jp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v_a_597_);
lean_ctor_set(v___x_602_, 0, v___y_605_);
v___x_607_ = v___x_602_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___y_605_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_a_597_);
v___x_607_ = v_reuseFailAlloc_609_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
v_a_596_ = v_tail_600_;
v_a_597_ = v___x_607_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4(lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
if (lean_obj_tag(v_a_629_) == 0)
{
lean_object* v___x_631_; 
v___x_631_ = l_List_reverse___redArg(v_a_630_);
return v___x_631_;
}
else
{
lean_object* v_head_632_; lean_object* v_tail_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_648_; 
v_head_632_ = lean_ctor_get(v_a_629_, 0);
v_tail_633_ = lean_ctor_get(v_a_629_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_a_629_);
if (v_isSharedCheck_648_ == 0)
{
v___x_635_ = v_a_629_;
v_isShared_636_ = v_isSharedCheck_648_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_tail_633_);
lean_inc(v_head_632_);
lean_dec(v_a_629_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_648_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_637_ = lean_array_to_list(v_head_632_);
v___x_638_ = lean_box(0);
v___x_639_ = l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3(v___x_637_, v___x_638_);
v___x_640_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__3));
v___x_641_ = l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(v___x_639_, v___x_640_);
v___x_642_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4___closed__1));
v___x_643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v_a_630_);
lean_ctor_set(v___x_635_, 0, v___x_643_);
v___x_645_ = v___x_635_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_a_630_);
v___x_645_ = v_reuseFailAlloc_647_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
v_a_629_ = v_tail_633_;
v_a_630_ = v___x_645_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_format(lean_object* v_info_649_){
_start:
{
lean_object* v_graph_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_graph_650_ = lean_ctor_get(v_info_649_, 0);
lean_inc_ref(v_graph_650_);
lean_dec_ref(v_info_649_);
v___x_651_ = lean_array_to_list(v_graph_650_);
v___x_652_ = lean_box(0);
v___x_653_ = l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4(v___x_651_, v___x_652_);
v___x_654_ = lean_box(1);
v___x_655_ = l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(v___x_653_, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0(lean_object* v_x_658_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = 0;
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0___boxed(lean_object* v_x_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0(v_x_660_);
lean_dec(v_x_660_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1(lean_object* v_fvarId_663_, lean_object* v_x_664_){
_start:
{
uint8_t v___x_665_; 
v___x_665_ = l_Lean_instBEqFVarId_beq(v_fvarId_663_, v_x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_666_, lean_object* v_x_667_){
_start:
{
uint8_t v_res_668_; lean_object* v_r_669_; 
v_res_668_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1(v_fvarId_666_, v_x_667_);
lean_dec(v_x_667_);
lean_dec(v_fvarId_666_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_671_; lean_object* v___x_672_; 
v_cellCount_671_ = lean_unsigned_to_nat(16u);
v___x_672_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_671_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_673_; lean_object* v___x_674_; 
v_cellCount_673_ = lean_unsigned_to_nat(16u);
v___x_674_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_676_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1);
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
lean_ctor_set(v___x_678_, 2, v___x_675_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(lean_object* v_e_679_, lean_object* v_fvarId_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; uint8_t v_fst_685_; lean_object* v_mctx_686_; lean_object* v___y_704_; lean_object* v_mctx_709_; lean_object* v___f_710_; lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_683_ = lean_st_ref_get(v___y_681_);
v_mctx_709_ = lean_ctor_get(v___x_683_, 0);
lean_inc_ref_n(v_mctx_709_, 2);
lean_dec(v___x_683_);
v___f_710_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__0));
v___f_711_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_711_, 0, v_fvarId_680_);
v___x_712_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__3, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__3_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__3);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v_mctx_709_);
v___x_714_ = l_Lean_Expr_hasFVar(v_e_679_);
if (v___x_714_ == 0)
{
uint8_t v___x_715_; 
v___x_715_ = l_Lean_Expr_hasMVar(v_e_679_);
if (v___x_715_ == 0)
{
lean_dec_ref_known(v___x_713_, 2);
lean_dec_ref(v___f_711_);
lean_dec_ref(v_e_679_);
v_fst_685_ = v___x_715_;
v_mctx_686_ = v_mctx_709_;
goto v___jp_684_;
}
else
{
lean_object* v___x_716_; 
lean_dec_ref(v_mctx_709_);
v___x_716_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_711_, v___f_710_, v_e_679_, v___x_713_);
v___y_704_ = v___x_716_;
goto v___jp_703_;
}
}
else
{
lean_object* v___x_717_; 
lean_dec_ref(v_mctx_709_);
v___x_717_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_711_, v___f_710_, v_e_679_, v___x_713_);
v___y_704_ = v___x_717_;
goto v___jp_703_;
}
v___jp_684_:
{
lean_object* v___x_687_; lean_object* v_cache_688_; lean_object* v_zetaDeltaFVarIds_689_; lean_object* v_postponed_690_; lean_object* v_diag_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_701_; 
v___x_687_ = lean_st_ref_take(v___y_681_);
v_cache_688_ = lean_ctor_get(v___x_687_, 1);
v_zetaDeltaFVarIds_689_ = lean_ctor_get(v___x_687_, 2);
v_postponed_690_ = lean_ctor_get(v___x_687_, 3);
v_diag_691_ = lean_ctor_get(v___x_687_, 4);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v___x_687_, 0);
lean_dec(v_unused_702_);
v___x_693_ = v___x_687_;
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_diag_691_);
lean_inc(v_postponed_690_);
lean_inc(v_zetaDeltaFVarIds_689_);
lean_inc(v_cache_688_);
lean_dec(v___x_687_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v_mctx_686_);
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_mctx_686_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_cache_688_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_zetaDeltaFVarIds_689_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_postponed_690_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_diag_691_);
v___x_696_ = v_reuseFailAlloc_700_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_st_ref_put(v___y_681_, v___x_696_);
v___x_698_ = lean_box(v_fst_685_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
}
v___jp_703_:
{
lean_object* v_snd_705_; lean_object* v_fst_706_; lean_object* v_mctx_707_; uint8_t v___x_708_; 
v_snd_705_ = lean_ctor_get(v___y_704_, 1);
lean_inc(v_snd_705_);
v_fst_706_ = lean_ctor_get(v___y_704_, 0);
lean_inc(v_fst_706_);
lean_dec_ref(v___y_704_);
v_mctx_707_ = lean_ctor_get(v_snd_705_, 1);
lean_inc_ref(v_mctx_707_);
lean_dec(v_snd_705_);
v___x_708_ = lean_unbox(v_fst_706_);
lean_dec(v_fst_706_);
v_fst_685_ = v___x_708_;
v_mctx_686_ = v_mctx_707_;
goto v___jp_684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___boxed(lean_object* v_e_718_, lean_object* v_fvarId_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_e_718_, v_fvarId_719_, v___y_720_);
lean_dec(v___y_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0(lean_object* v_e_723_, lean_object* v_fvarId_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_e_723_, v_fvarId_724_, v___y_726_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___boxed(lean_object* v_e_731_, lean_object* v_fvarId_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0(v_e_731_, v_fvarId_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0(lean_object* v_k_739_, lean_object* v_b_740_, lean_object* v_c_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; 
lean_inc(v___y_745_);
lean_inc_ref(v___y_744_);
lean_inc(v___y_743_);
lean_inc_ref(v___y_742_);
v___x_747_ = lean_apply_7(v_k_739_, v_b_740_, v_c_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, lean_box(0));
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed(lean_object* v_k_748_, lean_object* v_b_749_, lean_object* v_c_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0(v_k_748_, v_b_749_, v_c_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(lean_object* v_e_757_, lean_object* v_k_758_, uint8_t v_cleanupAnnotations_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___f_765_; uint8_t v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___f_765_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_765_, 0, v_k_758_);
v___x_766_ = 1;
v___x_767_ = 0;
v___x_768_ = lean_box(0);
v___x_769_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_757_, v___x_766_, v___x_767_, v___x_766_, v___x_767_, v___x_768_, v___f_765_, v_cleanupAnnotations_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_a_778_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_769_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_769_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___boxed(lean_object* v_e_786_, lean_object* v_k_787_, lean_object* v_cleanupAnnotations_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_794_; lean_object* v_res_795_; 
v_cleanupAnnotations_boxed_794_ = lean_unbox(v_cleanupAnnotations_788_);
v_res_795_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_e_786_, v_k_787_, v_cleanupAnnotations_boxed_794_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3(lean_object* v_00_u03b1_796_, lean_object* v_e_797_, lean_object* v_k_798_, uint8_t v_cleanupAnnotations_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_e_797_, v_k_798_, v_cleanupAnnotations_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___boxed(lean_object* v_00_u03b1_806_, lean_object* v_e_807_, lean_object* v_k_808_, lean_object* v_cleanupAnnotations_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_815_; lean_object* v_res_816_; 
v_cleanupAnnotations_boxed_815_ = lean_unbox(v_cleanupAnnotations_809_);
v_res_816_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3(v_00_u03b1_806_, v_e_807_, v_k_808_, v_cleanupAnnotations_boxed_815_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(lean_object* v_upperBound_817_, lean_object* v_xs_818_, lean_object* v_next_819_, lean_object* v_a_820_, lean_object* v_b_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = lean_nat_dec_lt(v_a_820_, v_upperBound_817_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_dec(v_a_820_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v_b_821_);
return v___x_828_;
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_array_fget_borrowed(v_xs_818_, v_a_820_);
lean_inc(v___y_825_);
lean_inc_ref(v___y_824_);
lean_inc(v___y_823_);
lean_inc_ref(v___y_822_);
lean_inc(v___x_829_);
v___x_830_ = lean_infer_type(v___x_829_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v___x_830_, 1);
v___x_832_ = lean_array_fget_borrowed(v_xs_818_, v_next_819_);
v___x_833_ = l_Lean_Expr_fvarId_x21(v___x_832_);
v___x_834_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_a_831_, v___x_833_, v___y_823_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v_a_837_; uint8_t v___x_841_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_834_, 1);
v___x_841_ = lean_unbox(v_a_835_);
lean_dec(v_a_835_);
if (v___x_841_ == 0)
{
v_a_837_ = v_b_821_;
goto v___jp_836_;
}
else
{
lean_object* v___x_842_; 
lean_inc(v_a_820_);
v___x_842_ = lean_array_push(v_b_821_, v_a_820_);
v_a_837_ = v___x_842_;
goto v___jp_836_;
}
v___jp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_nat_add(v_a_820_, v___x_838_);
lean_dec(v_a_820_);
v_a_820_ = v___x_839_;
v_b_821_ = v_a_837_;
goto _start;
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec_ref(v_b_821_);
lean_dec(v_a_820_);
v_a_843_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_834_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_834_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v_b_821_);
lean_dec(v_a_820_);
v_a_851_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_830_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_830_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg___boxed(lean_object* v_upperBound_859_, lean_object* v_xs_860_, lean_object* v_next_861_, lean_object* v_a_862_, lean_object* v_b_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v_upperBound_859_, v_xs_860_, v_next_861_, v_a_862_, v_b_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v_next_861_);
lean_dec_ref(v_xs_860_);
lean_dec(v_upperBound_859_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(lean_object* v_upperBound_872_, lean_object* v___x_873_, lean_object* v_xs_874_, lean_object* v_a_875_, lean_object* v_b_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
uint8_t v___x_882_; 
v___x_882_ = lean_nat_dec_lt(v_a_875_, v_upperBound_872_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
lean_dec(v_a_875_);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v_b_876_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_nat_add(v_a_875_, v___x_884_);
v___x_886_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg___closed__0));
lean_inc(v___x_885_);
v___x_887_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v___x_873_, v_xs_874_, v_a_875_, v___x_885_, v___x_886_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v_a_875_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v___x_889_ = lean_array_push(v_b_876_, v_a_888_);
v_a_875_ = v___x_885_;
v_b_876_ = v___x_889_;
goto _start;
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec(v___x_885_);
lean_dec_ref(v_b_876_);
v_a_891_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_887_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_887_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg___boxed(lean_object* v_upperBound_899_, lean_object* v___x_900_, lean_object* v_xs_901_, lean_object* v_a_902_, lean_object* v_b_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v_upperBound_899_, v___x_900_, v_xs_901_, v_a_902_, v_b_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec_ref(v_xs_901_);
lean_dec(v___x_900_);
lean_dec(v_upperBound_899_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___lam__0(lean_object* v_xs_912_, lean_object* v_x_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v_revDeps_921_; lean_object* v___x_922_; 
v___x_919_ = lean_array_get_size(v_xs_912_);
v___x_920_ = lean_unsigned_to_nat(0u);
v_revDeps_921_ = ((lean_object*)(l_Lean_Elab_getParamRevDeps___lam__0___closed__0));
v___x_922_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v___x_919_, v___x_919_, v_xs_912_, v___x_920_, v_revDeps_921_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___lam__0___boxed(lean_object* v_xs_923_, lean_object* v_x_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Elab_getParamRevDeps___lam__0(v_xs_923_, v_x_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_x_924_);
lean_dec_ref(v_xs_923_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps(lean_object* v_value_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v___f_938_; uint8_t v___x_939_; lean_object* v___x_940_; 
v___f_938_ = ((lean_object*)(l_Lean_Elab_getParamRevDeps___closed__0));
v___x_939_ = 1;
v___x_940_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_932_, v___f_938_, v___x_939_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___boxed(lean_object* v_value_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Elab_getParamRevDeps(v_value_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1(lean_object* v_upperBound_948_, lean_object* v_xs_949_, lean_object* v_next_950_, lean_object* v_inst_951_, lean_object* v_R_952_, lean_object* v_a_953_, lean_object* v_b_954_, lean_object* v_c_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v_upperBound_948_, v_xs_949_, v_next_950_, v_a_953_, v_b_954_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___boxed(lean_object* v_upperBound_962_, lean_object* v_xs_963_, lean_object* v_next_964_, lean_object* v_inst_965_, lean_object* v_R_966_, lean_object* v_a_967_, lean_object* v_b_968_, lean_object* v_c_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1(v_upperBound_962_, v_xs_963_, v_next_964_, v_inst_965_, v_R_966_, v_a_967_, v_b_968_, v_c_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v_next_964_);
lean_dec_ref(v_xs_963_);
lean_dec(v_upperBound_962_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2(lean_object* v_upperBound_976_, lean_object* v___x_977_, lean_object* v_xs_978_, lean_object* v_inst_979_, lean_object* v_R_980_, lean_object* v_a_981_, lean_object* v_b_982_, lean_object* v_c_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v_upperBound_976_, v___x_977_, v_xs_978_, v_a_981_, v_b_982_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___boxed(lean_object* v_upperBound_990_, lean_object* v___x_991_, lean_object* v_xs_992_, lean_object* v_inst_993_, lean_object* v_R_994_, lean_object* v_a_995_, lean_object* v_b_996_, lean_object* v_c_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2(v_upperBound_990_, v___x_991_, v_xs_992_, v_inst_993_, v_R_994_, v_a_995_, v_b_996_, v_c_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec_ref(v_xs_992_);
lean_dec(v___x_991_);
lean_dec(v_upperBound_990_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(lean_object* v_msg_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___f_1011_; lean_object* v___x_30953__overap_1012_; lean_object* v___x_1013_; 
v___f_1011_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_30953__overap_1012_ = lean_panic_fn_borrowed(v___f_1011_, v_msg_1005_);
lean_inc(v___y_1009_);
lean_inc_ref(v___y_1008_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
v___x_1013_ = lean_apply_5(v___x_30953__overap_1012_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, lean_box(0));
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___boxed(lean_object* v_msg_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v_msg_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(size_t v_sz_1021_, size_t v_i_1022_, lean_object* v_bs_1023_){
_start:
{
uint8_t v___x_1024_; 
v___x_1024_ = lean_usize_dec_lt(v_i_1022_, v_sz_1021_);
if (v___x_1024_ == 0)
{
return v_bs_1023_;
}
else
{
lean_object* v_v_1025_; lean_object* v___x_1026_; lean_object* v_bs_x27_1027_; lean_object* v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v_v_1025_ = lean_array_uget(v_bs_1023_, v_i_1022_);
v___x_1026_ = lean_unsigned_to_nat(0u);
v_bs_x27_1027_ = lean_array_uset(v_bs_1023_, v_i_1022_, v___x_1026_);
v___x_1028_ = lean_array_get_size(v_v_1025_);
lean_dec(v_v_1025_);
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_add(v_i_1022_, v___x_1029_);
v___x_1031_ = lean_array_uset(v_bs_x27_1027_, v_i_1022_, v___x_1028_);
v_i_1022_ = v___x_1030_;
v_bs_1023_ = v___x_1031_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1___boxed(lean_object* v_sz_1033_, lean_object* v_i_1034_, lean_object* v_bs_1035_){
_start:
{
size_t v_sz_boxed_1036_; size_t v_i_boxed_1037_; lean_object* v_res_1038_; 
v_sz_boxed_1036_ = lean_unbox_usize(v_sz_1033_);
lean_dec(v_sz_1033_);
v_i_boxed_1037_ = lean_unbox_usize(v_i_1034_);
lean_dec(v_i_1034_);
v_res_1038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_boxed_1036_, v_i_boxed_1037_, v_bs_1035_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(size_t v_sz_1039_, size_t v_i_1040_, lean_object* v_bs_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
uint8_t v___x_1047_; 
v___x_1047_ = lean_usize_dec_lt(v_i_1040_, v_sz_1039_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_bs_1041_);
return v___x_1048_;
}
else
{
lean_object* v_v_1049_; lean_object* v_value_1050_; lean_object* v___x_1051_; 
v_v_1049_ = lean_array_uget_borrowed(v_bs_1041_, v_i_1040_);
v_value_1050_ = lean_ctor_get(v_v_1049_, 7);
lean_inc_ref(v_value_1050_);
v___x_1051_ = l_Lean_Elab_getParamRevDeps(v_value_1050_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; lean_object* v_bs_x27_1054_; size_t v___x_1055_; size_t v___x_1056_; lean_object* v___x_1057_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = lean_unsigned_to_nat(0u);
v_bs_x27_1054_ = lean_array_uset(v_bs_1041_, v_i_1040_, v___x_1053_);
v___x_1055_ = ((size_t)1ULL);
v___x_1056_ = lean_usize_add(v_i_1040_, v___x_1055_);
v___x_1057_ = lean_array_uset(v_bs_x27_1054_, v_i_1040_, v_a_1052_);
v_i_1040_ = v___x_1056_;
v_bs_1041_ = v___x_1057_;
goto _start;
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v_bs_1041_);
v_a_1059_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1051_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1051_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0___boxed(lean_object* v_sz_1067_, lean_object* v_i_1068_, lean_object* v_bs_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
size_t v_sz_boxed_1075_; size_t v_i_boxed_1076_; lean_object* v_res_1077_; 
v_sz_boxed_1075_ = lean_unbox_usize(v_sz_1067_);
lean_dec(v_sz_1067_);
v_i_boxed_1076_ = lean_unbox_usize(v_i_1068_);
lean_dec(v_i_1068_);
v_res_1077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_boxed_1075_, v_i_boxed_1076_, v_bs_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(lean_object* v_msgData_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; lean_object* v_env_1085_; lean_object* v___x_1086_; lean_object* v_mctx_1087_; lean_object* v_lctx_1088_; lean_object* v_options_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1084_ = lean_st_ref_get(v___y_1082_);
v_env_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_ref(v_env_1085_);
lean_dec(v___x_1084_);
v___x_1086_ = lean_st_ref_get(v___y_1080_);
v_mctx_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc_ref(v_mctx_1087_);
lean_dec(v___x_1086_);
v_lctx_1088_ = lean_ctor_get(v___y_1079_, 2);
v_options_1089_ = lean_ctor_get(v___y_1081_, 2);
lean_inc_ref(v_options_1089_);
lean_inc_ref(v_lctx_1088_);
v___x_1090_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1090_, 0, v_env_1085_);
lean_ctor_set(v___x_1090_, 1, v_mctx_1087_);
lean_ctor_set(v___x_1090_, 2, v_lctx_1088_);
lean_ctor_set(v___x_1090_, 3, v_options_1089_);
v___x_1091_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v_msgData_1078_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2___boxed(lean_object* v_msgData_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msgData_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1100_; double v___x_1101_; 
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = lean_float_of_nat(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(lean_object* v_cls_1105_, lean_object* v_msg_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_ref_1112_; lean_object* v___x_1113_; lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1158_; 
v_ref_1112_ = lean_ctor_get(v___y_1109_, 5);
v___x_1113_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msg_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1158_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1158_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v_traceState_1119_; lean_object* v_env_1120_; lean_object* v_nextMacroScope_1121_; lean_object* v_ngen_1122_; lean_object* v_auxDeclNGen_1123_; lean_object* v_cache_1124_; lean_object* v_messages_1125_; lean_object* v_infoState_1126_; lean_object* v_snapshotTasks_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1157_; 
v___x_1118_ = lean_st_ref_take(v___y_1110_);
v_traceState_1119_ = lean_ctor_get(v___x_1118_, 4);
v_env_1120_ = lean_ctor_get(v___x_1118_, 0);
v_nextMacroScope_1121_ = lean_ctor_get(v___x_1118_, 1);
v_ngen_1122_ = lean_ctor_get(v___x_1118_, 2);
v_auxDeclNGen_1123_ = lean_ctor_get(v___x_1118_, 3);
v_cache_1124_ = lean_ctor_get(v___x_1118_, 5);
v_messages_1125_ = lean_ctor_get(v___x_1118_, 6);
v_infoState_1126_ = lean_ctor_get(v___x_1118_, 7);
v_snapshotTasks_1127_ = lean_ctor_get(v___x_1118_, 8);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1129_ = v___x_1118_;
v_isShared_1130_ = v_isSharedCheck_1157_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_snapshotTasks_1127_);
lean_inc(v_infoState_1126_);
lean_inc(v_messages_1125_);
lean_inc(v_cache_1124_);
lean_inc(v_traceState_1119_);
lean_inc(v_auxDeclNGen_1123_);
lean_inc(v_ngen_1122_);
lean_inc(v_nextMacroScope_1121_);
lean_inc(v_env_1120_);
lean_dec(v___x_1118_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1157_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint64_t v_tid_1131_; lean_object* v_traces_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1156_; 
v_tid_1131_ = lean_ctor_get_uint64(v_traceState_1119_, sizeof(void*)*1);
v_traces_1132_ = lean_ctor_get(v_traceState_1119_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_traceState_1119_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1134_ = v_traceState_1119_;
v_isShared_1135_ = v_isSharedCheck_1156_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_traces_1132_);
lean_dec(v_traceState_1119_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1156_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; double v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0);
v___x_1138_ = 0;
v___x_1139_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1));
v___x_1140_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1140_, 0, v_cls_1105_);
lean_ctor_set(v___x_1140_, 1, v___x_1136_);
lean_ctor_set(v___x_1140_, 2, v___x_1139_);
lean_ctor_set_float(v___x_1140_, sizeof(void*)*3, v___x_1137_);
lean_ctor_set_float(v___x_1140_, sizeof(void*)*3 + 8, v___x_1137_);
lean_ctor_set_uint8(v___x_1140_, sizeof(void*)*3 + 16, v___x_1138_);
v___x_1141_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2));
v___x_1142_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v_a_1114_);
lean_ctor_set(v___x_1142_, 2, v___x_1141_);
lean_inc(v_ref_1112_);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v_ref_1112_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_PersistentArray_push___redArg(v_traces_1132_, v___x_1143_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1144_);
v___x_1146_ = v___x_1134_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1144_);
lean_ctor_set_uint64(v_reuseFailAlloc_1155_, sizeof(void*)*1, v_tid_1131_);
v___x_1146_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 4, v___x_1146_);
v___x_1148_ = v___x_1129_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_env_1120_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_nextMacroScope_1121_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_ngen_1122_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v_auxDeclNGen_1123_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1154_, 5, v_cache_1124_);
lean_ctor_set(v_reuseFailAlloc_1154_, 6, v_messages_1125_);
lean_ctor_set(v_reuseFailAlloc_1154_, 7, v_infoState_1126_);
lean_ctor_set(v_reuseFailAlloc_1154_, 8, v_snapshotTasks_1127_);
v___x_1148_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1149_ = lean_st_ref_put(v___y_1110_, v___x_1148_);
v___x_1150_ = lean_box(0);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1150_);
v___x_1152_ = v___x_1116_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___boxed(lean_object* v_cls_1159_, lean_object* v_msg_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v_cls_1159_, v_msg_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_object* v_00_u03b1_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_apply_1(v_x_1168_, lean_box(0));
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0___boxed(lean_object* v_00_u03b1_1176_, lean_object* v_x_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(v_00_u03b1_1176_, v_x_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(lean_object* v_m_1184_, lean_object* v_query_1185_, lean_object* v_x_1186_, lean_object* v_x_1187_, lean_object* v_x_1188_){
_start:
{
lean_object* v_zero_1189_; uint8_t v_isZero_1190_; 
v_zero_1189_ = lean_unsigned_to_nat(0u);
v_isZero_1190_ = lean_nat_dec_eq(v_x_1187_, v_zero_1189_);
if (v_isZero_1190_ == 1)
{
lean_dec(v_x_1188_);
lean_dec(v_x_1187_);
if (lean_obj_tag(v_x_1186_) == 0)
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_box(2);
return v___x_1191_;
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_val_1192_ = lean_ctor_get(v_x_1186_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_x_1186_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v_x_1186_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_val_1192_);
lean_dec(v_x_1186_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_val_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_keyArray_1200_; lean_object* v_valueArray_1201_; lean_object* v___x_1202_; uint8_t v_isSome_1203_; 
v_keyArray_1200_ = lean_ctor_get(v_m_1184_, 1);
v_valueArray_1201_ = lean_ctor_get(v_m_1184_, 2);
v___x_1202_ = lean_array_fget_borrowed(v_keyArray_1200_, v_x_1188_);
v_isSome_1203_ = lean_noption_is_some(v___x_1202_);
if (v_isSome_1203_ == 0)
{
lean_dec(v_x_1187_);
if (lean_obj_tag(v_x_1186_) == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1204_, 0, v_x_1188_);
return v___x_1204_;
}
else
{
lean_object* v_val_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v_x_1188_);
v_val_1205_ = lean_ctor_get(v_x_1186_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_x_1186_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v_x_1186_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_val_1205_);
lean_dec(v_x_1186_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_val_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_object* v_one_1213_; lean_object* v_n_1214_; lean_object* v___y_1216_; 
v_one_1213_ = lean_unsigned_to_nat(1u);
v_n_1214_ = lean_nat_sub(v_x_1187_, v_one_1213_);
lean_dec(v_x_1187_);
if (v_isSome_1203_ == 0)
{
goto v___jp_1222_;
}
else
{
lean_object* v___x_1224_; uint8_t v_isSome_1225_; 
v___x_1224_ = lean_array_fget_borrowed(v_valueArray_1201_, v_x_1188_);
v_isSome_1225_ = lean_noption_is_some(v___x_1224_);
if (v_isSome_1225_ == 0)
{
goto v___jp_1222_;
}
else
{
lean_object* v_val_1226_; uint8_t v___x_1227_; 
lean_inc(v___x_1202_);
v_val_1226_ = lean_noption_get(v___x_1202_);
v___x_1227_ = l_Lean_ExprStructEq_beq(v_val_1226_, v_query_1185_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
lean_dec(v_val_1226_);
v___x_1228_ = lean_array_get_size(v_keyArray_1200_);
v___x_1229_ = lean_nat_add(v_x_1188_, v_one_1213_);
lean_dec(v_x_1188_);
v___x_1230_ = lean_nat_dec_lt(v___x_1229_, v___x_1228_);
if (v___x_1230_ == 0)
{
lean_dec(v___x_1229_);
v_x_1187_ = v_n_1214_;
v_x_1188_ = v_zero_1189_;
goto _start;
}
else
{
v_x_1187_ = v_n_1214_;
v_x_1188_ = v___x_1229_;
goto _start;
}
}
else
{
lean_object* v_val_1233_; lean_object* v___x_1234_; 
lean_dec(v_n_1214_);
lean_dec(v_x_1186_);
lean_inc(v___x_1224_);
v_val_1233_ = lean_noption_get(v___x_1224_);
v___x_1234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1234_, 0, v_x_1188_);
lean_ctor_set(v___x_1234_, 1, v_val_1226_);
lean_ctor_set(v___x_1234_, 2, v_val_1233_);
return v___x_1234_;
}
}
}
v___jp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1217_ = lean_array_get_size(v_keyArray_1200_);
v___x_1218_ = lean_nat_add(v_x_1188_, v_one_1213_);
lean_dec(v_x_1188_);
v___x_1219_ = lean_nat_dec_lt(v___x_1218_, v___x_1217_);
if (v___x_1219_ == 0)
{
lean_dec(v___x_1218_);
v_x_1186_ = v___y_1216_;
v_x_1187_ = v_n_1214_;
v_x_1188_ = v_zero_1189_;
goto _start;
}
else
{
v_x_1186_ = v___y_1216_;
v_x_1187_ = v_n_1214_;
v_x_1188_ = v___x_1218_;
goto _start;
}
}
v___jp_1222_:
{
if (lean_obj_tag(v_x_1186_) == 0)
{
lean_object* v___x_1223_; 
lean_inc(v_x_1188_);
v___x_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1223_, 0, v_x_1188_);
v___y_1216_ = v___x_1223_;
goto v___jp_1215_;
}
else
{
v___y_1216_ = v_x_1186_;
goto v___jp_1215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg___boxed(lean_object* v_m_1235_, lean_object* v_query_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_, lean_object* v_x_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_m_1235_, v_query_1236_, v_x_1237_, v_x_1238_, v_x_1239_);
lean_dec_ref(v_query_1236_);
lean_dec_ref(v_m_1235_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(lean_object* v_m_1241_, lean_object* v_query_1242_){
_start:
{
lean_object* v_keyArray_1243_; lean_object* v___x_1244_; uint64_t v___x_1245_; uint64_t v___x_1246_; uint64_t v___x_1247_; uint64_t v_fold_1248_; uint64_t v___x_1249_; uint64_t v___x_1250_; uint64_t v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_keyArray_1243_ = lean_ctor_get(v_m_1241_, 1);
v___x_1244_ = lean_array_get_size(v_keyArray_1243_);
v___x_1245_ = l_Lean_ExprStructEq_hash(v_query_1242_);
v___x_1246_ = 32ULL;
v___x_1247_ = lean_uint64_shift_right(v___x_1245_, v___x_1246_);
v_fold_1248_ = lean_uint64_xor(v___x_1245_, v___x_1247_);
v___x_1249_ = 16ULL;
v___x_1250_ = lean_uint64_shift_right(v_fold_1248_, v___x_1249_);
v___x_1251_ = lean_uint64_xor(v_fold_1248_, v___x_1250_);
v___x_1252_ = lean_uint64_to_usize(v___x_1251_);
v___x_1253_ = lean_usize_of_nat(v___x_1244_);
v___x_1254_ = ((size_t)1ULL);
v___x_1255_ = lean_usize_sub(v___x_1253_, v___x_1254_);
v___x_1256_ = lean_usize_land(v___x_1252_, v___x_1255_);
v___x_1257_ = lean_usize_to_nat(v___x_1256_);
v___x_1258_ = lean_box(0);
v___x_1259_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_m_1241_, v_query_1242_, v___x_1258_, v___x_1244_, v___x_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg___boxed(lean_object* v_m_1260_, lean_object* v_query_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_1260_, v_query_1261_);
lean_dec_ref(v_query_1261_);
lean_dec_ref(v_m_1260_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27_spec__28___redArg(lean_object* v_b_1263_, lean_object* v_acc_1264_, lean_object* v_i_1265_){
_start:
{
lean_object* v___y_1267_; lean_object* v_keyArray_1275_; lean_object* v_valueArray_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v_keyArray_1275_ = lean_ctor_get(v_b_1263_, 1);
v_valueArray_1276_ = lean_ctor_get(v_b_1263_, 2);
v___x_1277_ = lean_array_get_size(v_keyArray_1275_);
v___x_1278_ = lean_nat_dec_lt(v_i_1265_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_dec(v_i_1265_);
return v_acc_1264_;
}
else
{
lean_object* v___x_1279_; uint8_t v_isSome_1280_; 
v___x_1279_ = lean_array_fget_borrowed(v_keyArray_1275_, v_i_1265_);
v_isSome_1280_ = lean_noption_is_some(v___x_1279_);
if (v_isSome_1280_ == 0)
{
goto v___jp_1271_;
}
else
{
lean_object* v___x_1281_; uint8_t v_isSome_1282_; 
v___x_1281_ = lean_array_fget_borrowed(v_valueArray_1276_, v_i_1265_);
v_isSome_1282_ = lean_noption_is_some(v___x_1281_);
if (v_isSome_1282_ == 0)
{
goto v___jp_1271_;
}
else
{
lean_object* v_val_1283_; lean_object* v_val_1284_; lean_object* v_i_1286_; lean_object* v___x_1291_; 
lean_inc(v___x_1279_);
v_val_1283_ = lean_noption_get(v___x_1279_);
lean_inc(v___x_1281_);
v_val_1284_ = lean_noption_get(v___x_1281_);
v___x_1291_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_acc_1264_, v_val_1283_);
switch(lean_obj_tag(v___x_1291_))
{
case 0:
{
lean_object* v_index_1292_; lean_object* v_size_1293_; lean_object* v___x_1294_; 
v_index_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_index_1292_);
lean_dec_ref_known(v___x_1291_, 3);
v_size_1293_ = lean_ctor_get(v_acc_1264_, 0);
lean_inc(v_size_1293_);
v___x_1294_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1264_, v_size_1293_, v_index_1292_, v_val_1283_, v_val_1284_);
lean_dec(v_index_1292_);
v___y_1267_ = v___x_1294_;
goto v___jp_1266_;
}
case 1:
{
lean_object* v_index_1295_; 
v_index_1295_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_index_1295_);
lean_dec_ref_known(v___x_1291_, 1);
v_i_1286_ = v_index_1295_;
goto v___jp_1285_;
}
default: 
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1264_, v___x_1296_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_index_1298_; 
v_index_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_index_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v_i_1286_ = v_index_1298_;
goto v___jp_1285_;
}
else
{
lean_dec(v_val_1284_);
lean_dec(v_val_1283_);
v___y_1267_ = v_acc_1264_;
goto v___jp_1266_;
}
}
}
v___jp_1285_:
{
lean_object* v_size_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_size_1287_ = lean_ctor_get(v_acc_1264_, 0);
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_nat_add(v_size_1287_, v___x_1288_);
v___x_1290_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1264_, v___x_1289_, v_i_1286_, v_val_1283_, v_val_1284_);
lean_dec(v_i_1286_);
v___y_1267_ = v___x_1290_;
goto v___jp_1266_;
}
}
}
}
v___jp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = lean_nat_add(v_i_1265_, v___x_1268_);
lean_dec(v_i_1265_);
v_acc_1264_ = v___y_1267_;
v_i_1265_ = v___x_1269_;
goto _start;
}
v___jp_1271_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_nat_add(v_i_1265_, v___x_1272_);
lean_dec(v_i_1265_);
v_i_1265_ = v___x_1273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27_spec__28___redArg___boxed(lean_object* v_b_1299_, lean_object* v_acc_1300_, lean_object* v_i_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27_spec__28___redArg(v_b_1299_, v_acc_1300_, v_i_1301_);
lean_dec_ref(v_b_1299_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27___redArg(lean_object* v_init_1303_, lean_object* v_b_1304_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27_spec__28___redArg(v_b_1304_, v_init_1303_, v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27___redArg___boxed(lean_object* v_init_1307_, lean_object* v_b_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27___redArg(v_init_1307_, v_b_1308_);
lean_dec_ref(v_b_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20___redArg(lean_object* v_m_1310_){
_start:
{
lean_object* v_keyArray_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_cellCount_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_target_1318_; lean_object* v___x_1319_; 
v_keyArray_1311_ = lean_ctor_get(v_m_1310_, 1);
v___x_1312_ = lean_array_get_size(v_keyArray_1311_);
v___x_1313_ = lean_unsigned_to_nat(2u);
v_cellCount_1314_ = lean_nat_mul(v___x_1312_, v___x_1313_);
v___x_1315_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1314_);
v___x_1316_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1314_);
v___x_1317_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1314_);
v_target_1318_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1318_, 0, v___x_1315_);
lean_ctor_set(v_target_1318_, 1, v___x_1316_);
lean_ctor_set(v_target_1318_, 2, v___x_1317_);
v___x_1319_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27___redArg(v_target_1318_, v_m_1310_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20___redArg___boxed(lean_object* v_m_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20___redArg(v_m_1320_);
lean_dec_ref(v_m_1320_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(lean_object* v_a_1322_, lean_object* v_e_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___y_1329_; lean_object* v___y_1332_; lean_object* v_i_1333_; lean_object* v___y_1349_; lean_object* v_i_1350_; lean_object* v___y_1356_; lean_object* v___x_1365_; 
v___x_1326_ = lean_st_ref_take(v_a_1322_);
v___x_1327_ = lean_box(0);
v___x_1365_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___x_1326_, v_e_1323_);
switch(lean_obj_tag(v___x_1365_))
{
case 0:
{
lean_object* v_index_1366_; lean_object* v_size_1367_; lean_object* v___x_1368_; 
v_index_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_index_1366_);
lean_dec_ref_known(v___x_1365_, 3);
v_size_1367_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_size_1367_);
v___x_1368_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1326_, v_size_1367_, v_index_1366_, v_e_1323_, v_a_1324_);
lean_dec(v_index_1366_);
v___y_1329_ = v___x_1368_;
goto v___jp_1328_;
}
case 1:
{
lean_object* v_index_1369_; lean_object* v_size_1370_; lean_object* v_keyArray_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v_index_1369_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_index_1369_);
lean_dec_ref_known(v___x_1365_, 1);
v_size_1370_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_size_1370_);
v_keyArray_1371_ = lean_ctor_get(v___x_1326_, 1);
lean_inc_ref(v_keyArray_1371_);
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_nat_add(v_size_1370_, v___x_1372_);
lean_dec(v_size_1370_);
v___x_1374_ = lean_array_get_size(v_keyArray_1371_);
lean_dec_ref(v_keyArray_1371_);
v___x_1375_ = lean_nat_dec_lt(v___x_1373_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_dec(v___x_1373_);
lean_dec(v_index_1369_);
goto v___jp_1338_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1376_ = lean_unsigned_to_nat(4u);
v___x_1377_ = lean_nat_mul(v___x_1373_, v___x_1376_);
v___x_1378_ = lean_unsigned_to_nat(3u);
v___x_1379_ = lean_nat_mul(v___x_1374_, v___x_1378_);
v___x_1380_ = lean_nat_dec_le(v___x_1377_, v___x_1379_);
lean_dec(v___x_1379_);
lean_dec(v___x_1377_);
if (v___x_1380_ == 0)
{
lean_dec(v___x_1373_);
lean_dec(v_index_1369_);
goto v___jp_1338_;
}
else
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1326_, v___x_1373_, v_index_1369_, v_e_1323_, v_a_1324_);
lean_dec(v_index_1369_);
v___y_1329_ = v___x_1381_;
goto v___jp_1328_;
}
}
}
default: 
{
lean_object* v_size_1382_; lean_object* v_keyArray_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_size_1382_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_size_1382_);
v_keyArray_1383_ = lean_ctor_get(v___x_1326_, 1);
lean_inc_ref(v_keyArray_1383_);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_add(v_size_1382_, v___x_1384_);
lean_dec(v_size_1382_);
v___x_1386_ = lean_array_get_size(v_keyArray_1383_);
lean_dec_ref(v_keyArray_1383_);
v___x_1387_ = lean_nat_dec_lt(v___x_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; 
lean_dec(v___x_1385_);
v___x_1388_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20___redArg(v___x_1326_);
lean_dec(v___x_1326_);
v___y_1356_ = v___x_1388_;
goto v___jp_1355_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1389_ = lean_unsigned_to_nat(4u);
v___x_1390_ = lean_nat_mul(v___x_1385_, v___x_1389_);
lean_dec(v___x_1385_);
v___x_1391_ = lean_unsigned_to_nat(3u);
v___x_1392_ = lean_nat_mul(v___x_1386_, v___x_1391_);
v___x_1393_ = lean_nat_dec_le(v___x_1390_, v___x_1392_);
lean_dec(v___x_1392_);
lean_dec(v___x_1390_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20___redArg(v___x_1326_);
lean_dec(v___x_1326_);
v___y_1356_ = v___x_1394_;
goto v___jp_1355_;
}
else
{
v___y_1356_ = v___x_1326_;
goto v___jp_1355_;
}
}
}
}
v___jp_1328_:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_st_ref_put(v_a_1322_, v___y_1329_);
return v___x_1327_;
}
v___jp_1331_:
{
lean_object* v_size_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_size_1334_ = lean_ctor_get(v___y_1332_, 0);
v___x_1335_ = lean_unsigned_to_nat(1u);
v___x_1336_ = lean_nat_add(v_size_1334_, v___x_1335_);
v___x_1337_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1332_, v___x_1336_, v_i_1333_, v_e_1323_, v_a_1324_);
lean_dec(v_i_1333_);
v___y_1329_ = v___x_1337_;
goto v___jp_1328_;
}
v___jp_1338_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20___redArg(v___x_1326_);
lean_dec(v___x_1326_);
v___x_1340_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___x_1339_, v_e_1323_);
switch(lean_obj_tag(v___x_1340_))
{
case 0:
{
lean_object* v_index_1341_; lean_object* v_size_1342_; lean_object* v___x_1343_; 
v_index_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_index_1341_);
lean_dec_ref_known(v___x_1340_, 3);
v_size_1342_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_size_1342_);
v___x_1343_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1339_, v_size_1342_, v_index_1341_, v_e_1323_, v_a_1324_);
lean_dec(v_index_1341_);
v___y_1329_ = v___x_1343_;
goto v___jp_1328_;
}
case 1:
{
lean_object* v_index_1344_; 
v_index_1344_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_index_1344_);
lean_dec_ref_known(v___x_1340_, 1);
v___y_1332_ = v___x_1339_;
v_i_1333_ = v_index_1344_;
goto v___jp_1331_;
}
default: 
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1339_, v___x_1345_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_index_1347_; 
v_index_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_index_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v___y_1332_ = v___x_1339_;
v_i_1333_ = v_index_1347_;
goto v___jp_1331_;
}
else
{
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_e_1323_);
v___y_1329_ = v___x_1339_;
goto v___jp_1328_;
}
}
}
}
v___jp_1348_:
{
lean_object* v_size_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_size_1351_ = lean_ctor_get(v___y_1349_, 0);
v___x_1352_ = lean_unsigned_to_nat(1u);
v___x_1353_ = lean_nat_add(v_size_1351_, v___x_1352_);
v___x_1354_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1349_, v___x_1353_, v_i_1350_, v_e_1323_, v_a_1324_);
lean_dec(v_i_1350_);
v___y_1329_ = v___x_1354_;
goto v___jp_1328_;
}
v___jp_1355_:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___y_1356_, v_e_1323_);
switch(lean_obj_tag(v___x_1357_))
{
case 0:
{
lean_object* v_index_1358_; lean_object* v_size_1359_; lean_object* v___x_1360_; 
v_index_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_index_1358_);
lean_dec_ref_known(v___x_1357_, 3);
v_size_1359_ = lean_ctor_get(v___y_1356_, 0);
lean_inc(v_size_1359_);
v___x_1360_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1356_, v_size_1359_, v_index_1358_, v_e_1323_, v_a_1324_);
lean_dec(v_index_1358_);
v___y_1329_ = v___x_1360_;
goto v___jp_1328_;
}
case 1:
{
lean_object* v_index_1361_; 
v_index_1361_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_index_1361_);
lean_dec_ref_known(v___x_1357_, 1);
v___y_1349_ = v___y_1356_;
v_i_1350_ = v_index_1361_;
goto v___jp_1348_;
}
default: 
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1356_, v___x_1362_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_index_1364_; 
v_index_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_index_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v___y_1349_ = v___y_1356_;
v_i_1350_ = v_index_1364_;
goto v___jp_1348_;
}
else
{
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_e_1323_);
v___y_1329_ = v___y_1356_;
goto v___jp_1328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed(lean_object* v_a_1395_, lean_object* v_e_1396_, lean_object* v_a_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(v_a_1395_, v_e_1396_, v_a_1397_);
lean_dec(v_a_1395_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(lean_object* v_k_1400_, lean_object* v___y_1401_, lean_object* v_b_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1401_);
v___x_1408_ = lean_apply_7(v_k_1400_, v_b_1402_, v___y_1401_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, lean_box(0));
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed(lean_object* v_k_1409_, lean_object* v___y_1410_, lean_object* v_b_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(v_k_1409_, v___y_1410_, v_b_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1410_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(lean_object* v_name_1418_, uint8_t v_bi_1419_, lean_object* v_type_1420_, lean_object* v_k_1421_, uint8_t v_kind_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___f_1429_; lean_object* v___x_1430_; 
lean_inc(v___y_1423_);
v___f_1429_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1429_, 0, v_k_1421_);
lean_closure_set(v___f_1429_, 1, v___y_1423_);
v___x_1430_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1418_, v_bi_1419_, v_type_1420_, v___f_1429_, v_kind_1422_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1430_) == 0)
{
return v___x_1430_;
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___boxed(lean_object* v_name_1439_, lean_object* v_bi_1440_, lean_object* v_type_1441_, lean_object* v_k_1442_, lean_object* v_kind_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
uint8_t v_bi_boxed_1450_; uint8_t v_kind_boxed_1451_; lean_object* v_res_1452_; 
v_bi_boxed_1450_ = lean_unbox(v_bi_1440_);
v_kind_boxed_1451_ = lean_unbox(v_kind_1443_);
v_res_1452_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_1439_, v_bi_boxed_1450_, v_type_1441_, v_k_1442_, v_kind_boxed_1451_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(lean_object* v___x_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1453_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed(lean_object* v___x_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(v___x_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(lean_object* v_name_1467_, lean_object* v_type_1468_, lean_object* v_val_1469_, lean_object* v_k_1470_, uint8_t v_nondep_1471_, uint8_t v_kind_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___f_1479_; lean_object* v___x_1480_; 
lean_inc(v___y_1473_);
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1479_, 0, v_k_1470_);
lean_closure_set(v___f_1479_, 1, v___y_1473_);
v___x_1480_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1467_, v_type_1468_, v_val_1469_, v___f_1479_, v_nondep_1471_, v_kind_1472_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1480_) == 0)
{
return v___x_1480_;
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg___boxed(lean_object* v_name_1489_, lean_object* v_type_1490_, lean_object* v_val_1491_, lean_object* v_k_1492_, lean_object* v_nondep_1493_, lean_object* v_kind_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
uint8_t v_nondep_boxed_1501_; uint8_t v_kind_boxed_1502_; lean_object* v_res_1503_; 
v_nondep_boxed_1501_ = lean_unbox(v_nondep_1493_);
v_kind_boxed_1502_ = lean_unbox(v_kind_1494_);
v_res_1503_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_1489_, v_type_1490_, v_val_1491_, v_k_1492_, v_nondep_boxed_1501_, v_kind_boxed_1502_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_object* v_00_u03b1_1504_, lean_object* v_x_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_apply_1(v_x_1505_, lean_box(0));
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0___boxed(lean_object* v_00_u03b1_1513_, lean_object* v_x_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(v_00_u03b1_1513_, v_x_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object* v_m_1521_, lean_object* v_query_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_1521_, v_query_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_index_1524_; lean_object* v_key_1525_; lean_object* v_value_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
v_index_1524_ = lean_ctor_get(v___x_1523_, 0);
v_key_1525_ = lean_ctor_get(v___x_1523_, 1);
v_value_1526_ = lean_ctor_get(v___x_1523_, 2);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1523_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_value_1526_);
lean_inc(v_key_1525_);
lean_inc(v_index_1524_);
lean_dec(v___x_1523_);
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
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_index_1524_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_key_1525_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_value_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
else
{
lean_object* v___x_1534_; 
lean_dec(v___x_1523_);
v___x_1534_ = lean_box(1);
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object* v_m_1535_, lean_object* v_query_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_m_1535_, v_query_1536_);
lean_dec_ref(v_query_1536_);
lean_dec_ref(v_m_1535_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_m_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_m_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_value_1541_; lean_object* v___x_1542_; 
v_value_1541_ = lean_ctor_get(v___x_1540_, 2);
lean_inc(v_value_1541_);
lean_dec_ref_known(v___x_1540_, 3);
v___x_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_value_1541_);
return v___x_1542_;
}
else
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_box(0);
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_m_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_1544_, v_a_1545_);
lean_dec_ref(v_a_1545_);
lean_dec_ref(v_m_1544_);
return v_res_1546_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = l_Lean_maxRecDepthErrorMessage;
v___x_1553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3);
v___x_1555_ = l_Lean_MessageData_ofFormat(v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4);
v___x_1557_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2));
v___x_1558_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v___x_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(lean_object* v_ref_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_ref_1559_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(lean_object* v_x_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___y_1575_; lean_object* v_fileName_1584_; lean_object* v_fileMap_1585_; lean_object* v_options_1586_; lean_object* v_currRecDepth_1587_; lean_object* v_maxRecDepth_1588_; lean_object* v_ref_1589_; lean_object* v_currNamespace_1590_; lean_object* v_openDecls_1591_; lean_object* v_initHeartbeats_1592_; lean_object* v_maxHeartbeats_1593_; lean_object* v_quotContext_1594_; lean_object* v_currMacroScope_1595_; uint8_t v_diag_1596_; lean_object* v_cancelTk_x3f_1597_; uint8_t v_suppressElabErrors_1598_; lean_object* v_inheritedTraceOptions_1599_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v_fileName_1584_ = lean_ctor_get(v___y_1571_, 0);
v_fileMap_1585_ = lean_ctor_get(v___y_1571_, 1);
v_options_1586_ = lean_ctor_get(v___y_1571_, 2);
v_currRecDepth_1587_ = lean_ctor_get(v___y_1571_, 3);
v_maxRecDepth_1588_ = lean_ctor_get(v___y_1571_, 4);
v_ref_1589_ = lean_ctor_get(v___y_1571_, 5);
v_currNamespace_1590_ = lean_ctor_get(v___y_1571_, 6);
v_openDecls_1591_ = lean_ctor_get(v___y_1571_, 7);
v_initHeartbeats_1592_ = lean_ctor_get(v___y_1571_, 8);
v_maxHeartbeats_1593_ = lean_ctor_get(v___y_1571_, 9);
v_quotContext_1594_ = lean_ctor_get(v___y_1571_, 10);
v_currMacroScope_1595_ = lean_ctor_get(v___y_1571_, 11);
v_diag_1596_ = lean_ctor_get_uint8(v___y_1571_, sizeof(void*)*14);
v_cancelTk_x3f_1597_ = lean_ctor_get(v___y_1571_, 12);
v_suppressElabErrors_1598_ = lean_ctor_get_uint8(v___y_1571_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1599_ = lean_ctor_get(v___y_1571_, 13);
v___x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = lean_nat_dec_eq(v_maxRecDepth_1588_, v___x_1605_);
if (v___x_1606_ == 0)
{
uint8_t v___x_1607_; 
v___x_1607_ = lean_nat_dec_eq(v_currRecDepth_1587_, v_maxRecDepth_1588_);
if (v___x_1607_ == 0)
{
goto v___jp_1600_;
}
else
{
lean_object* v___x_1608_; 
lean_dec_ref(v_x_1567_);
lean_inc(v_ref_1589_);
v___x_1608_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1589_);
v___y_1575_ = v___x_1608_;
goto v___jp_1574_;
}
}
else
{
goto v___jp_1600_;
}
v___jp_1574_:
{
if (lean_obj_tag(v___y_1575_) == 0)
{
return v___y_1575_;
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_a_1576_ = lean_ctor_get(v___y_1575_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___y_1575_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___y_1575_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___y_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
v___jp_1600_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1601_ = lean_unsigned_to_nat(1u);
v___x_1602_ = lean_nat_add(v_currRecDepth_1587_, v___x_1601_);
lean_inc_ref(v_inheritedTraceOptions_1599_);
lean_inc(v_cancelTk_x3f_1597_);
lean_inc(v_currMacroScope_1595_);
lean_inc(v_quotContext_1594_);
lean_inc(v_maxHeartbeats_1593_);
lean_inc(v_initHeartbeats_1592_);
lean_inc(v_openDecls_1591_);
lean_inc(v_currNamespace_1590_);
lean_inc(v_ref_1589_);
lean_inc(v_maxRecDepth_1588_);
lean_inc_ref(v_options_1586_);
lean_inc_ref(v_fileMap_1585_);
lean_inc_ref(v_fileName_1584_);
v___x_1603_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1603_, 0, v_fileName_1584_);
lean_ctor_set(v___x_1603_, 1, v_fileMap_1585_);
lean_ctor_set(v___x_1603_, 2, v_options_1586_);
lean_ctor_set(v___x_1603_, 3, v___x_1602_);
lean_ctor_set(v___x_1603_, 4, v_maxRecDepth_1588_);
lean_ctor_set(v___x_1603_, 5, v_ref_1589_);
lean_ctor_set(v___x_1603_, 6, v_currNamespace_1590_);
lean_ctor_set(v___x_1603_, 7, v_openDecls_1591_);
lean_ctor_set(v___x_1603_, 8, v_initHeartbeats_1592_);
lean_ctor_set(v___x_1603_, 9, v_maxHeartbeats_1593_);
lean_ctor_set(v___x_1603_, 10, v_quotContext_1594_);
lean_ctor_set(v___x_1603_, 11, v_currMacroScope_1595_);
lean_ctor_set(v___x_1603_, 12, v_cancelTk_x3f_1597_);
lean_ctor_set(v___x_1603_, 13, v_inheritedTraceOptions_1599_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*14, v_diag_1596_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*14 + 1, v_suppressElabErrors_1598_);
lean_inc(v___y_1572_);
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
lean_inc(v___y_1568_);
v___x_1604_ = lean_apply_6(v_x_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___x_1603_, v___y_1572_, lean_box(0));
v___y_1575_ = v___x_1604_;
goto v___jp_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1620_, lean_object* v_pre_1621_, lean_object* v_post_1622_, uint8_t v_usedLetOnly_1623_, uint8_t v_skipConstInApp_1624_, uint8_t v_skipInstances_1625_, lean_object* v_body_1626_, lean_object* v_x_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_array_push(v_fvars_1620_, v_x_1627_);
v___x_1635_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1621_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v___x_1634_, v_body_1626_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1636_, lean_object* v_pre_1637_, lean_object* v_post_1638_, lean_object* v_usedLetOnly_1639_, lean_object* v_skipConstInApp_1640_, lean_object* v_skipInstances_1641_, lean_object* v_body_1642_, lean_object* v_x_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
uint8_t v_usedLetOnly_boxed_1650_; uint8_t v_skipConstInApp_boxed_1651_; uint8_t v_skipInstances_boxed_1652_; lean_object* v_res_1653_; 
v_usedLetOnly_boxed_1650_ = lean_unbox(v_usedLetOnly_1639_);
v_skipConstInApp_boxed_1651_ = lean_unbox(v_skipConstInApp_1640_);
v_skipInstances_boxed_1652_ = lean_unbox(v_skipInstances_1641_);
v_res_1653_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1636_, v_pre_1637_, v_post_1638_, v_usedLetOnly_boxed_1650_, v_skipConstInApp_boxed_1651_, v_skipInstances_boxed_1652_, v_body_1642_, v_x_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1654_, lean_object* v_post_1655_, uint8_t v_usedLetOnly_1656_, uint8_t v_skipConstInApp_1657_, uint8_t v_skipInstances_1658_, lean_object* v_e_1659_, lean_object* v_a_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; 
lean_inc_ref(v_post_1655_);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1663_);
lean_inc(v___y_1662_);
lean_inc_ref(v___y_1661_);
lean_inc_ref(v_e_1659_);
v___x_1666_ = lean_apply_6(v_post_1655_, v_e_1659_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, lean_box(0));
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1685_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1685_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1685_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
switch(lean_obj_tag(v_a_1667_))
{
case 0:
{
lean_object* v_e_1671_; lean_object* v___x_1673_; 
lean_dec_ref(v_e_1659_);
lean_dec_ref(v_post_1655_);
lean_dec_ref(v_pre_1654_);
v_e_1671_ = lean_ctor_get(v_a_1667_, 0);
lean_inc_ref(v_e_1671_);
lean_dec_ref_known(v_a_1667_, 1);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v_e_1671_);
v___x_1673_ = v___x_1669_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_e_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
case 1:
{
lean_object* v_e_1675_; lean_object* v___x_1676_; 
lean_del_object(v___x_1669_);
lean_dec_ref(v_e_1659_);
v_e_1675_ = lean_ctor_get(v_a_1667_, 0);
lean_inc_ref(v_e_1675_);
lean_dec_ref_known(v_a_1667_, 1);
v___x_1676_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1654_, v_post_1655_, v_usedLetOnly_1656_, v_skipConstInApp_1657_, v_skipInstances_1658_, v_e_1675_, v_a_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
return v___x_1676_;
}
default: 
{
lean_object* v_e_x3f_1677_; 
lean_dec_ref(v_post_1655_);
lean_dec_ref(v_pre_1654_);
v_e_x3f_1677_ = lean_ctor_get(v_a_1667_, 0);
lean_inc(v_e_x3f_1677_);
lean_dec_ref_known(v_a_1667_, 1);
if (lean_obj_tag(v_e_x3f_1677_) == 0)
{
lean_object* v___x_1679_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v_e_1659_);
v___x_1679_ = v___x_1669_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_e_1659_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
else
{
lean_object* v_val_1681_; lean_object* v___x_1683_; 
lean_dec_ref(v_e_1659_);
v_val_1681_ = lean_ctor_get(v_e_x3f_1677_, 0);
lean_inc(v_val_1681_);
lean_dec_ref_known(v_e_x3f_1677_, 1);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v_val_1681_);
v___x_1683_ = v___x_1669_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_val_1681_);
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
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref(v_e_1659_);
lean_dec_ref(v_post_1655_);
lean_dec_ref(v_pre_1654_);
v_a_1686_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1666_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1666_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1694_, lean_object* v_post_1695_, uint8_t v_usedLetOnly_1696_, uint8_t v_skipConstInApp_1697_, uint8_t v_skipInstances_1698_, lean_object* v_fvars_1699_, lean_object* v_e_1700_, lean_object* v_a_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
if (lean_obj_tag(v_e_1700_) == 6)
{
lean_object* v_binderName_1707_; lean_object* v_binderType_1708_; lean_object* v_body_1709_; uint8_t v_binderInfo_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_binderName_1707_ = lean_ctor_get(v_e_1700_, 0);
lean_inc(v_binderName_1707_);
v_binderType_1708_ = lean_ctor_get(v_e_1700_, 1);
lean_inc_ref(v_binderType_1708_);
v_body_1709_ = lean_ctor_get(v_e_1700_, 2);
lean_inc_ref(v_body_1709_);
v_binderInfo_1710_ = lean_ctor_get_uint8(v_e_1700_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1700_, 3);
v___x_1711_ = lean_expr_instantiate_rev(v_binderType_1708_, v_fvars_1699_);
lean_dec_ref(v_binderType_1708_);
lean_inc_ref(v_post_1695_);
lean_inc_ref(v_pre_1694_);
v___x_1712_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1694_, v_post_1695_, v_usedLetOnly_1696_, v_skipConstInApp_1697_, v_skipInstances_1698_, v___x_1711_, v_a_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___f_1717_; uint8_t v___x_1718_; lean_object* v___x_1719_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = lean_box(v_usedLetOnly_1696_);
v___x_1715_ = lean_box(v_skipConstInApp_1697_);
v___x_1716_ = lean_box(v_skipInstances_1698_);
v___f_1717_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1717_, 0, v_fvars_1699_);
lean_closure_set(v___f_1717_, 1, v_pre_1694_);
lean_closure_set(v___f_1717_, 2, v_post_1695_);
lean_closure_set(v___f_1717_, 3, v___x_1714_);
lean_closure_set(v___f_1717_, 4, v___x_1715_);
lean_closure_set(v___f_1717_, 5, v___x_1716_);
lean_closure_set(v___f_1717_, 6, v_body_1709_);
v___x_1718_ = 0;
v___x_1719_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1707_, v_binderInfo_1710_, v_a_1713_, v___f_1717_, v___x_1718_, v_a_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1719_;
}
else
{
lean_dec_ref(v_body_1709_);
lean_dec(v_binderName_1707_);
lean_dec_ref(v_fvars_1699_);
lean_dec_ref(v_post_1695_);
lean_dec_ref(v_pre_1694_);
return v___x_1712_;
}
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_expr_instantiate_rev(v_e_1700_, v_fvars_1699_);
lean_dec_ref(v_e_1700_);
lean_inc_ref(v_post_1695_);
lean_inc_ref(v_pre_1694_);
v___x_1721_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1694_, v_post_1695_, v_usedLetOnly_1696_, v_skipConstInApp_1697_, v_skipInstances_1698_, v___x_1720_, v_a_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; uint8_t v___x_1723_; uint8_t v___x_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = 0;
v___x_1724_ = 1;
v___x_1725_ = 1;
v___x_1726_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1699_, v_a_1722_, v___x_1723_, v_usedLetOnly_1696_, v___x_1723_, v___x_1724_, v___x_1725_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec_ref(v_fvars_1699_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1694_, v_post_1695_, v_usedLetOnly_1696_, v_skipConstInApp_1697_, v_skipInstances_1698_, v_a_1727_, v_a_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1728_;
}
else
{
lean_dec_ref(v_post_1695_);
lean_dec_ref(v_pre_1694_);
return v___x_1726_;
}
}
else
{
lean_dec_ref(v_fvars_1699_);
lean_dec_ref(v_post_1695_);
lean_dec_ref(v_pre_1694_);
return v___x_1721_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1729_, lean_object* v_pre_1730_, lean_object* v_post_1731_, uint8_t v_usedLetOnly_1732_, uint8_t v_skipConstInApp_1733_, uint8_t v_skipInstances_1734_, lean_object* v_body_1735_, lean_object* v_x_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_array_push(v_fvars_1729_, v_x_1736_);
v___x_1744_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1730_, v_post_1731_, v_usedLetOnly_1732_, v_skipConstInApp_1733_, v_skipInstances_1734_, v___x_1743_, v_body_1735_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1745_, lean_object* v_pre_1746_, lean_object* v_post_1747_, lean_object* v_usedLetOnly_1748_, lean_object* v_skipConstInApp_1749_, lean_object* v_skipInstances_1750_, lean_object* v_body_1751_, lean_object* v_x_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v_usedLetOnly_boxed_1759_; uint8_t v_skipConstInApp_boxed_1760_; uint8_t v_skipInstances_boxed_1761_; lean_object* v_res_1762_; 
v_usedLetOnly_boxed_1759_ = lean_unbox(v_usedLetOnly_1748_);
v_skipConstInApp_boxed_1760_ = lean_unbox(v_skipConstInApp_1749_);
v_skipInstances_boxed_1761_ = lean_unbox(v_skipInstances_1750_);
v_res_1762_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1745_, v_pre_1746_, v_post_1747_, v_usedLetOnly_boxed_1759_, v_skipConstInApp_boxed_1760_, v_skipInstances_boxed_1761_, v_body_1751_, v_x_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1763_, lean_object* v_post_1764_, uint8_t v_usedLetOnly_1765_, uint8_t v_skipConstInApp_1766_, uint8_t v_skipInstances_1767_, lean_object* v_fvars_1768_, lean_object* v_e_1769_, lean_object* v_a_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
if (lean_obj_tag(v_e_1769_) == 8)
{
lean_object* v_declName_1776_; lean_object* v_type_1777_; lean_object* v_value_1778_; lean_object* v_body_1779_; uint8_t v_nondep_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_declName_1776_ = lean_ctor_get(v_e_1769_, 0);
lean_inc(v_declName_1776_);
v_type_1777_ = lean_ctor_get(v_e_1769_, 1);
lean_inc_ref(v_type_1777_);
v_value_1778_ = lean_ctor_get(v_e_1769_, 2);
lean_inc_ref(v_value_1778_);
v_body_1779_ = lean_ctor_get(v_e_1769_, 3);
lean_inc_ref(v_body_1779_);
v_nondep_1780_ = lean_ctor_get_uint8(v_e_1769_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1769_, 4);
v___x_1781_ = lean_expr_instantiate_rev(v_type_1777_, v_fvars_1768_);
lean_dec_ref(v_type_1777_);
lean_inc_ref(v_post_1764_);
lean_inc_ref(v_pre_1763_);
v___x_1782_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1763_, v_post_1764_, v_usedLetOnly_1765_, v_skipConstInApp_1766_, v_skipInstances_1767_, v___x_1781_, v_a_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v___x_1784_ = lean_expr_instantiate_rev(v_value_1778_, v_fvars_1768_);
lean_dec_ref(v_value_1778_);
lean_inc_ref(v_post_1764_);
lean_inc_ref(v_pre_1763_);
v___x_1785_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1763_, v_post_1764_, v_usedLetOnly_1765_, v_skipConstInApp_1766_, v_skipInstances_1767_, v___x_1784_, v_a_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___f_1790_; uint8_t v___x_1791_; lean_object* v___x_1792_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v___x_1787_ = lean_box(v_usedLetOnly_1765_);
v___x_1788_ = lean_box(v_skipConstInApp_1766_);
v___x_1789_ = lean_box(v_skipInstances_1767_);
v___f_1790_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1790_, 0, v_fvars_1768_);
lean_closure_set(v___f_1790_, 1, v_pre_1763_);
lean_closure_set(v___f_1790_, 2, v_post_1764_);
lean_closure_set(v___f_1790_, 3, v___x_1787_);
lean_closure_set(v___f_1790_, 4, v___x_1788_);
lean_closure_set(v___f_1790_, 5, v___x_1789_);
lean_closure_set(v___f_1790_, 6, v_body_1779_);
v___x_1791_ = 0;
v___x_1792_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1776_, v_a_1783_, v_a_1786_, v___f_1790_, v_nondep_1780_, v___x_1791_, v_a_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
return v___x_1792_;
}
else
{
lean_dec(v_a_1783_);
lean_dec_ref(v_body_1779_);
lean_dec(v_declName_1776_);
lean_dec_ref(v_fvars_1768_);
lean_dec_ref(v_post_1764_);
lean_dec_ref(v_pre_1763_);
return v___x_1785_;
}
}
else
{
lean_dec_ref(v_body_1779_);
lean_dec_ref(v_value_1778_);
lean_dec(v_declName_1776_);
lean_dec_ref(v_fvars_1768_);
lean_dec_ref(v_post_1764_);
lean_dec_ref(v_pre_1763_);
return v___x_1782_;
}
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_expr_instantiate_rev(v_e_1769_, v_fvars_1768_);
lean_dec_ref(v_e_1769_);
lean_inc_ref(v_post_1764_);
lean_inc_ref(v_pre_1763_);
v___x_1794_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1763_, v_post_1764_, v_usedLetOnly_1765_, v_skipConstInApp_1766_, v_skipInstances_1767_, v___x_1793_, v_a_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; uint8_t v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1794_, 1);
v___x_1796_ = 0;
v___x_1797_ = 1;
v___x_1798_ = l_Lean_Meta_mkLetFVars(v_fvars_1768_, v_a_1795_, v_usedLetOnly_1765_, v___x_1796_, v___x_1797_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec_ref(v_fvars_1768_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1800_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1798_, 1);
v___x_1800_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1763_, v_post_1764_, v_usedLetOnly_1765_, v_skipConstInApp_1766_, v_skipInstances_1767_, v_a_1799_, v_a_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
return v___x_1800_;
}
else
{
lean_dec_ref(v_post_1764_);
lean_dec_ref(v_pre_1763_);
return v___x_1798_;
}
}
else
{
lean_dec_ref(v_fvars_1768_);
lean_dec_ref(v_post_1764_);
lean_dec_ref(v_pre_1763_);
return v___x_1794_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1801_; lean_object* v_dummy_1802_; 
v___x_1801_ = lean_box(0);
v_dummy_1802_ = l_Lean_Expr_sort___override(v___x_1801_);
return v_dummy_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1803_, lean_object* v_post_1804_, uint8_t v_usedLetOnly_1805_, uint8_t v_skipConstInApp_1806_, uint8_t v_skipInstances_1807_, size_t v_sz_1808_, size_t v_i_1809_, lean_object* v_bs_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_usize_dec_lt(v_i_1809_, v_sz_1808_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; 
lean_dec_ref(v_post_1804_);
lean_dec_ref(v_pre_1803_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v_bs_1810_);
return v___x_1818_;
}
else
{
lean_object* v_v_1819_; lean_object* v___x_1820_; 
v_v_1819_ = lean_array_uget_borrowed(v_bs_1810_, v_i_1809_);
lean_inc(v_v_1819_);
lean_inc_ref(v_post_1804_);
lean_inc_ref(v_pre_1803_);
v___x_1820_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1803_, v_post_1804_, v_usedLetOnly_1805_, v_skipConstInApp_1806_, v_skipInstances_1807_, v_v_1819_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1822_; lean_object* v_bs_x27_1823_; size_t v___x_1824_; size_t v___x_1825_; lean_object* v___x_1826_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1820_, 1);
v___x_1822_ = lean_unsigned_to_nat(0u);
v_bs_x27_1823_ = lean_array_uset(v_bs_1810_, v_i_1809_, v___x_1822_);
v___x_1824_ = ((size_t)1ULL);
v___x_1825_ = lean_usize_add(v_i_1809_, v___x_1824_);
v___x_1826_ = lean_array_uset(v_bs_x27_1823_, v_i_1809_, v_a_1821_);
v_i_1809_ = v___x_1825_;
v_bs_1810_ = v___x_1826_;
goto _start;
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec_ref(v_bs_1810_);
lean_dec_ref(v_post_1804_);
lean_dec_ref(v_pre_1803_);
v_a_1828_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1820_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1820_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1836_, lean_object* v_post_1837_, uint8_t v_usedLetOnly_1838_, uint8_t v_skipConstInApp_1839_, uint8_t v_skipInstances_1840_, lean_object* v___x_1841_, lean_object* v___y_1842_, lean_object* v_b_1843_, lean_object* v_a_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1836_, v_post_1837_, v_usedLetOnly_1838_, v_skipConstInApp_1839_, v_skipInstances_1840_, v___x_1841_, v___y_1842_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1860_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1860_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1860_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1855_ = lean_array_fset(v_b_1843_, v_a_1844_, v_a_1851_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1856_);
v___x_1858_ = v___x_1853_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_b_1843_);
v_a_1861_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1850_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1850_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1869_, lean_object* v_post_1870_, lean_object* v_usedLetOnly_1871_, lean_object* v_skipConstInApp_1872_, lean_object* v_skipInstances_1873_, lean_object* v___x_1874_, lean_object* v___y_1875_, lean_object* v_b_1876_, lean_object* v_a_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
uint8_t v_usedLetOnly_boxed_1883_; uint8_t v_skipConstInApp_boxed_1884_; uint8_t v_skipInstances_boxed_1885_; lean_object* v_res_1886_; 
v_usedLetOnly_boxed_1883_ = lean_unbox(v_usedLetOnly_1871_);
v_skipConstInApp_boxed_1884_ = lean_unbox(v_skipConstInApp_1872_);
v_skipInstances_boxed_1885_ = lean_unbox(v_skipInstances_1873_);
v_res_1886_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1869_, v_post_1870_, v_usedLetOnly_boxed_1883_, v_skipConstInApp_boxed_1884_, v_skipInstances_boxed_1885_, v___x_1874_, v___y_1875_, v_b_1876_, v_a_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v_a_1877_);
lean_dec(v___y_1875_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1887_, lean_object* v___x_1888_, lean_object* v_pre_1889_, lean_object* v_post_1890_, uint8_t v_usedLetOnly_1891_, uint8_t v_skipConstInApp_1892_, uint8_t v_skipInstances_1893_, lean_object* v_a_1894_, lean_object* v_b_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___y_1903_; uint8_t v___x_1926_; 
v___x_1926_ = lean_nat_dec_lt(v_a_1894_, v_upperBound_1887_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
lean_dec(v_a_1894_);
lean_dec_ref(v_post_1890_);
lean_dec_ref(v_pre_1889_);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_b_1895_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1928_ = lean_array_fget_borrowed(v_b_1895_, v_a_1894_);
v___x_1929_ = lean_array_get_size(v___x_1888_);
v___x_1930_ = lean_nat_dec_lt(v_a_1894_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; 
lean_inc(v___x_1928_);
v___x_1931_ = lean_box(v_usedLetOnly_1891_);
v___x_1932_ = lean_box(v_skipConstInApp_1892_);
v___x_1933_ = lean_box(v_skipInstances_1893_);
lean_inc(v_a_1894_);
lean_inc(v___y_1896_);
lean_inc_ref(v_post_1890_);
lean_inc_ref(v_pre_1889_);
v___f_1934_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1934_, 0, v_pre_1889_);
lean_closure_set(v___f_1934_, 1, v_post_1890_);
lean_closure_set(v___f_1934_, 2, v___x_1931_);
lean_closure_set(v___f_1934_, 3, v___x_1932_);
lean_closure_set(v___f_1934_, 4, v___x_1933_);
lean_closure_set(v___f_1934_, 5, v___x_1928_);
lean_closure_set(v___f_1934_, 6, v___y_1896_);
lean_closure_set(v___f_1934_, 7, v_b_1895_);
lean_closure_set(v___f_1934_, 8, v_a_1894_);
v___y_1903_ = v___f_1934_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1935_; uint8_t v_isInstance_1936_; 
v___x_1935_ = lean_array_fget_borrowed(v___x_1888_, v_a_1894_);
v_isInstance_1936_ = lean_ctor_get_uint8(v___x_1935_, sizeof(void*)*1 + 4);
if (v_isInstance_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___f_1940_; 
lean_inc(v___x_1928_);
v___x_1937_ = lean_box(v_usedLetOnly_1891_);
v___x_1938_ = lean_box(v_skipConstInApp_1892_);
v___x_1939_ = lean_box(v_skipInstances_1893_);
lean_inc(v_a_1894_);
lean_inc(v___y_1896_);
lean_inc_ref(v_post_1890_);
lean_inc_ref(v_pre_1889_);
v___f_1940_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1940_, 0, v_pre_1889_);
lean_closure_set(v___f_1940_, 1, v_post_1890_);
lean_closure_set(v___f_1940_, 2, v___x_1937_);
lean_closure_set(v___f_1940_, 3, v___x_1938_);
lean_closure_set(v___f_1940_, 4, v___x_1939_);
lean_closure_set(v___f_1940_, 5, v___x_1928_);
lean_closure_set(v___f_1940_, 6, v___y_1896_);
lean_closure_set(v___f_1940_, 7, v_b_1895_);
lean_closure_set(v___f_1940_, 8, v_a_1894_);
v___y_1903_ = v___f_1940_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1941_; lean_object* v___f_1942_; 
v___x_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1941_, 0, v_b_1895_);
v___f_1942_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1942_, 0, v___x_1941_);
v___y_1903_ = v___f_1942_;
goto v___jp_1902_;
}
}
}
v___jp_1902_:
{
lean_object* v___x_1904_; 
lean_inc(v___y_1900_);
lean_inc_ref(v___y_1899_);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
v___x_1904_ = lean_apply_5(v___y_1903_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, lean_box(0));
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1917_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1917_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1917_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
if (lean_obj_tag(v_a_1905_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; 
lean_dec(v_a_1894_);
lean_dec_ref(v_post_1890_);
lean_dec_ref(v_pre_1889_);
v_a_1909_ = lean_ctor_get(v_a_1905_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v_a_1905_, 1);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v_a_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
lean_del_object(v___x_1907_);
v_a_1913_ = lean_ctor_get(v_a_1905_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v_a_1905_, 1);
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_nat_add(v_a_1894_, v___x_1914_);
lean_dec(v_a_1894_);
v_a_1894_ = v___x_1915_;
v_b_1895_ = v_a_1913_;
goto _start;
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v_a_1894_);
lean_dec_ref(v_post_1890_);
lean_dec_ref(v_pre_1889_);
v_a_1918_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1904_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1904_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1943_, lean_object* v_pre_1944_, lean_object* v_post_1945_, uint8_t v_usedLetOnly_1946_, uint8_t v_skipConstInApp_1947_, lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_f_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; 
if (lean_obj_tag(v_x_1948_) == 5)
{
lean_object* v_fn_2006_; lean_object* v_arg_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_fn_2006_ = lean_ctor_get(v_x_1948_, 0);
lean_inc_ref(v_fn_2006_);
v_arg_2007_ = lean_ctor_get(v_x_1948_, 1);
lean_inc_ref(v_arg_2007_);
lean_dec_ref_known(v_x_1948_, 2);
v___x_2008_ = lean_array_set(v_x_1949_, v_x_1950_, v_arg_2007_);
v___x_2009_ = lean_unsigned_to_nat(1u);
v___x_2010_ = lean_nat_sub(v_x_1950_, v___x_2009_);
lean_dec(v_x_1950_);
v_x_1948_ = v_fn_2006_;
v_x_1949_ = v___x_2008_;
v_x_1950_ = v___x_2010_;
goto _start;
}
else
{
lean_dec(v_x_1950_);
if (v_skipConstInApp_1947_ == 0)
{
goto v___jp_2003_;
}
else
{
uint8_t v___x_2012_; 
v___x_2012_ = l_Lean_Expr_isConst(v_x_1948_);
if (v___x_2012_ == 0)
{
goto v___jp_2003_;
}
else
{
v_f_1958_ = v_x_1948_;
v___y_1959_ = v___y_1951_;
v___y_1960_ = v___y_1952_;
v___y_1961_ = v___y_1953_;
v___y_1962_ = v___y_1954_;
v___y_1963_ = v___y_1955_;
goto v___jp_1957_;
}
}
}
v___jp_1957_:
{
if (v_skipInstances_1943_ == 0)
{
size_t v_sz_1964_; size_t v___x_1965_; lean_object* v___x_1966_; 
v_sz_1964_ = lean_array_size(v_x_1949_);
v___x_1965_ = ((size_t)0ULL);
lean_inc_ref(v_post_1945_);
lean_inc_ref(v_pre_1944_);
v___x_1966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1944_, v_post_1945_, v_usedLetOnly_1946_, v_skipConstInApp_1947_, v_skipInstances_1943_, v_sz_1964_, v___x_1965_, v_x_1949_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v___x_1968_ = l_Lean_mkAppN(v_f_1958_, v_a_1967_);
lean_dec(v_a_1967_);
v___x_1969_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1944_, v_post_1945_, v_usedLetOnly_1946_, v_skipConstInApp_1947_, v_skipInstances_1943_, v___x_1968_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1969_;
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v_f_1958_);
lean_dec_ref(v_post_1945_);
lean_dec_ref(v_pre_1944_);
v_a_1970_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1966_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1966_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_array_get_size(v_x_1949_);
lean_inc_ref(v_f_1958_);
v___x_1979_ = l_Lean_Meta_getFunInfoNArgs(v_f_1958_, v___x_1978_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v_paramInfo_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v_paramInfo_1981_ = lean_ctor_get(v_a_1980_, 0);
lean_inc_ref(v_paramInfo_1981_);
lean_dec(v_a_1980_);
v___x_1982_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1945_);
lean_inc_ref(v_pre_1944_);
v___x_1983_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1978_, v_paramInfo_1981_, v_pre_1944_, v_post_1945_, v_usedLetOnly_1946_, v_skipConstInApp_1947_, v_skipInstances_1943_, v___x_1982_, v_x_1949_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec_ref(v_paramInfo_1981_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1983_, 1);
v___x_1985_ = l_Lean_mkAppN(v_f_1958_, v_a_1984_);
lean_dec(v_a_1984_);
v___x_1986_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1944_, v_post_1945_, v_usedLetOnly_1946_, v_skipConstInApp_1947_, v_skipInstances_1943_, v___x_1985_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1986_;
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec_ref(v_f_1958_);
lean_dec_ref(v_post_1945_);
lean_dec_ref(v_pre_1944_);
v_a_1987_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1983_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1983_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v_f_1958_);
lean_dec_ref(v_x_1949_);
lean_dec_ref(v_post_1945_);
lean_dec_ref(v_pre_1944_);
v_a_1995_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1979_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1979_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
v___jp_2003_:
{
lean_object* v___x_2004_; 
lean_inc_ref(v_post_1945_);
lean_inc_ref(v_pre_1944_);
v___x_2004_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1944_, v_post_1945_, v_usedLetOnly_1946_, v_skipConstInApp_1947_, v_skipInstances_1943_, v_x_1948_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v_f_1958_ = v_a_2005_;
v___y_1959_ = v___y_1951_;
v___y_1960_ = v___y_1952_;
v___y_1961_ = v___y_1953_;
v___y_1962_ = v___y_1954_;
v___y_1963_ = v___y_1955_;
goto v___jp_1957_;
}
else
{
lean_dec_ref(v_x_1949_);
lean_dec_ref(v_post_1945_);
lean_dec_ref(v_pre_1944_);
return v___x_2004_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_2013_, lean_object* v_pre_2014_, lean_object* v_e_2015_, lean_object* v_post_2016_, uint8_t v_usedLetOnly_2017_, uint8_t v_skipConstInApp_2018_, uint8_t v_skipInstances_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_Core_checkSystem(v___x_2013_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2027_; 
lean_dec_ref_known(v___x_2026_, 1);
lean_inc_ref(v_pre_2014_);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
lean_inc_ref(v_e_2015_);
v___x_2027_ = lean_apply_6(v_pre_2014_, v_e_2015_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, lean_box(0));
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2076_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2076_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2076_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___y_2033_; 
switch(lean_obj_tag(v_a_2028_))
{
case 0:
{
lean_object* v_e_2068_; lean_object* v___x_2070_; 
lean_dec_ref(v_post_2016_);
lean_dec_ref(v_e_2015_);
lean_dec_ref(v_pre_2014_);
v_e_2068_ = lean_ctor_get(v_a_2028_, 0);
lean_inc_ref(v_e_2068_);
lean_dec_ref_known(v_a_2028_, 1);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v_e_2068_);
v___x_2070_ = v___x_2030_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_e_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
case 1:
{
lean_object* v_e_2072_; lean_object* v___x_2073_; 
lean_del_object(v___x_2030_);
lean_dec_ref(v_e_2015_);
v_e_2072_ = lean_ctor_get(v_a_2028_, 0);
lean_inc_ref(v_e_2072_);
lean_dec_ref_known(v_a_2028_, 1);
v___x_2073_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2014_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v_e_2072_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2073_;
}
default: 
{
lean_object* v_e_x3f_2074_; 
lean_del_object(v___x_2030_);
v_e_x3f_2074_ = lean_ctor_get(v_a_2028_, 0);
lean_inc(v_e_x3f_2074_);
lean_dec_ref_known(v_a_2028_, 1);
if (lean_obj_tag(v_e_x3f_2074_) == 0)
{
v___y_2033_ = v_e_2015_;
goto v___jp_2032_;
}
else
{
lean_object* v_val_2075_; 
lean_dec_ref(v_e_2015_);
v_val_2075_ = lean_ctor_get(v_e_x3f_2074_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v_e_x3f_2074_, 1);
v___y_2033_ = v_val_2075_;
goto v___jp_2032_;
}
}
}
v___jp_2032_:
{
switch(lean_obj_tag(v___y_2033_))
{
case 7:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_2035_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2014_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v___x_2034_, v___y_2033_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2035_;
}
case 6:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_2037_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2014_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v___x_2036_, v___y_2033_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2037_;
}
case 8:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_2039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2014_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v___x_2038_, v___y_2033_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2039_;
}
case 5:
{
lean_object* v_dummy_2040_; lean_object* v_nargs_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_dummy_2040_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2041_ = l_Lean_Expr_getAppNumArgs(v___y_2033_);
lean_inc(v_nargs_2041_);
v___x_2042_ = lean_mk_array(v_nargs_2041_, v_dummy_2040_);
v___x_2043_ = lean_unsigned_to_nat(1u);
v___x_2044_ = lean_nat_sub(v_nargs_2041_, v___x_2043_);
lean_dec(v_nargs_2041_);
v___x_2045_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_2019_, v_pre_2014_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v___y_2033_, v___x_2042_, v___x_2044_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2045_;
}
case 10:
{
lean_object* v_data_2046_; lean_object* v_expr_2047_; lean_object* v___x_2048_; 
v_data_2046_ = lean_ctor_get(v___y_2033_, 0);
v_expr_2047_ = lean_ctor_get(v___y_2033_, 1);
lean_inc_ref(v_expr_2047_);
lean_inc_ref(v_post_2016_);
lean_inc_ref(v_pre_2014_);
v___x_2048_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2014_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v_expr_2047_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; size_t v___x_2050_; size_t v___x_2051_; uint8_t v___x_2052_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2048_, 1);
v___x_2050_ = lean_ptr_addr(v_expr_2047_);
v___x_2051_ = lean_ptr_addr(v_a_2049_);
v___x_2052_ = lean_usize_dec_eq(v___x_2050_, v___x_2051_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_inc(v_data_2046_);
lean_dec_ref_known(v___y_2033_, 2);
v___x_2053_ = l_Lean_Expr_mdata___override(v_data_2046_, v_a_2049_);
v___x_2054_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2014_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v___x_2053_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2054_;
}
else
{
lean_object* v___x_2055_; 
lean_dec(v_a_2049_);
v___x_2055_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2014_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v___y_2033_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2055_;
}
}
else
{
lean_dec_ref_known(v___y_2033_, 2);
lean_dec_ref(v_post_2016_);
lean_dec_ref(v_pre_2014_);
return v___x_2048_;
}
}
case 11:
{
lean_object* v_typeName_2056_; lean_object* v_idx_2057_; lean_object* v_struct_2058_; lean_object* v___x_2059_; 
v_typeName_2056_ = lean_ctor_get(v___y_2033_, 0);
v_idx_2057_ = lean_ctor_get(v___y_2033_, 1);
v_struct_2058_ = lean_ctor_get(v___y_2033_, 2);
lean_inc_ref(v_struct_2058_);
lean_inc_ref(v_post_2016_);
lean_inc_ref(v_pre_2014_);
v___x_2059_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2014_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v_struct_2058_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; size_t v___x_2061_; size_t v___x_2062_; uint8_t v___x_2063_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2059_, 1);
v___x_2061_ = lean_ptr_addr(v_struct_2058_);
v___x_2062_ = lean_ptr_addr(v_a_2060_);
v___x_2063_ = lean_usize_dec_eq(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_inc(v_idx_2057_);
lean_inc(v_typeName_2056_);
lean_dec_ref_known(v___y_2033_, 3);
v___x_2064_ = l_Lean_Expr_proj___override(v_typeName_2056_, v_idx_2057_, v_a_2060_);
v___x_2065_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2014_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v___x_2064_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2065_;
}
else
{
lean_object* v___x_2066_; 
lean_dec(v_a_2060_);
v___x_2066_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2014_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v___y_2033_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2066_;
}
}
else
{
lean_dec_ref_known(v___y_2033_, 3);
lean_dec_ref(v_post_2016_);
lean_dec_ref(v_pre_2014_);
return v___x_2059_;
}
}
default: 
{
lean_object* v___x_2067_; 
v___x_2067_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2014_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v___y_2033_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2067_;
}
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref(v_post_2016_);
lean_dec_ref(v_e_2015_);
lean_dec_ref(v_pre_2014_);
v_a_2077_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2027_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2027_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v_post_2016_);
lean_dec_ref(v_e_2015_);
lean_dec_ref(v_pre_2014_);
v_a_2085_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2026_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2026_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2093_, lean_object* v_pre_2094_, lean_object* v_e_2095_, lean_object* v_post_2096_, lean_object* v_usedLetOnly_2097_, lean_object* v_skipConstInApp_2098_, lean_object* v_skipInstances_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
uint8_t v_usedLetOnly_boxed_2106_; uint8_t v_skipConstInApp_boxed_2107_; uint8_t v_skipInstances_boxed_2108_; lean_object* v_res_2109_; 
v_usedLetOnly_boxed_2106_ = lean_unbox(v_usedLetOnly_2097_);
v_skipConstInApp_boxed_2107_ = lean_unbox(v_skipConstInApp_2098_);
v_skipInstances_boxed_2108_ = lean_unbox(v_skipInstances_2099_);
v_res_2109_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2093_, v_pre_2094_, v_e_2095_, v_post_2096_, v_usedLetOnly_boxed_2106_, v_skipConstInApp_boxed_2107_, v_skipInstances_boxed_2108_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2110_, lean_object* v_post_2111_, uint8_t v_usedLetOnly_2112_, uint8_t v_skipConstInApp_2113_, uint8_t v_skipInstances_2114_, lean_object* v_e_2115_, lean_object* v_a_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_inc(v_a_2116_);
v___x_2122_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2122_, 0, lean_box(0));
lean_closure_set(v___x_2122_, 1, lean_box(0));
lean_closure_set(v___x_2122_, 2, v_a_2116_);
v___x_2123_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2122_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2158_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2158_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2158_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_2124_, v_e_2115_);
lean_dec(v_a_2124_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___f_2133_; lean_object* v___x_2134_; 
lean_del_object(v___x_2126_);
v___x_2129_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2130_ = lean_box(v_usedLetOnly_2112_);
v___x_2131_ = lean_box(v_skipConstInApp_2113_);
v___x_2132_ = lean_box(v_skipInstances_2114_);
lean_inc_ref(v_e_2115_);
v___f_2133_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2133_, 0, v___x_2129_);
lean_closure_set(v___f_2133_, 1, v_pre_2110_);
lean_closure_set(v___f_2133_, 2, v_e_2115_);
lean_closure_set(v___f_2133_, 3, v_post_2111_);
lean_closure_set(v___f_2133_, 4, v___x_2130_);
lean_closure_set(v___f_2133_, 5, v___x_2131_);
lean_closure_set(v___f_2133_, 6, v___x_2132_);
v___x_2134_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2133_, v_a_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___f_2136_; lean_object* v___x_2137_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc_n(v_a_2135_, 2);
lean_dec_ref_known(v___x_2134_, 1);
lean_inc(v_a_2116_);
v___f_2136_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2136_, 0, v_a_2116_);
lean_closure_set(v___f_2136_, 1, v_e_2115_);
lean_closure_set(v___f_2136_, 2, v_a_2135_);
v___x_2137_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2136_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; 
v_unused_2145_ = lean_ctor_get(v___x_2137_, 0);
lean_dec(v_unused_2145_);
v___x_2139_ = v___x_2137_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_dec(v___x_2137_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v_a_2135_);
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2135_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_a_2135_);
v_a_2146_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2137_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2137_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_dec_ref(v_e_2115_);
return v___x_2134_;
}
}
else
{
lean_object* v_val_2154_; lean_object* v___x_2156_; 
lean_dec_ref(v_e_2115_);
lean_dec_ref(v_post_2111_);
lean_dec_ref(v_pre_2110_);
v_val_2154_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_val_2154_);
lean_dec_ref_known(v___x_2128_, 1);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v_val_2154_);
v___x_2156_ = v___x_2126_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_val_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec_ref(v_e_2115_);
lean_dec_ref(v_post_2111_);
lean_dec_ref(v_pre_2110_);
v_a_2159_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2123_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2123_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_2167_, lean_object* v_pre_2168_, lean_object* v_post_2169_, lean_object* v_usedLetOnly_2170_, lean_object* v_skipConstInApp_2171_, lean_object* v_skipInstances_2172_, lean_object* v_body_2173_, lean_object* v_x_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
uint8_t v_usedLetOnly_boxed_2181_; uint8_t v_skipConstInApp_boxed_2182_; uint8_t v_skipInstances_boxed_2183_; lean_object* v_res_2184_; 
v_usedLetOnly_boxed_2181_ = lean_unbox(v_usedLetOnly_2170_);
v_skipConstInApp_boxed_2182_ = lean_unbox(v_skipConstInApp_2171_);
v_skipInstances_boxed_2183_ = lean_unbox(v_skipInstances_2172_);
v_res_2184_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_2167_, v_pre_2168_, v_post_2169_, v_usedLetOnly_boxed_2181_, v_skipConstInApp_boxed_2182_, v_skipInstances_boxed_2183_, v_body_2173_, v_x_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2185_, lean_object* v_post_2186_, uint8_t v_usedLetOnly_2187_, uint8_t v_skipConstInApp_2188_, uint8_t v_skipInstances_2189_, lean_object* v_fvars_2190_, lean_object* v_e_2191_, lean_object* v_a_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
if (lean_obj_tag(v_e_2191_) == 7)
{
lean_object* v_binderName_2198_; lean_object* v_binderType_2199_; lean_object* v_body_2200_; uint8_t v_binderInfo_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_binderName_2198_ = lean_ctor_get(v_e_2191_, 0);
lean_inc(v_binderName_2198_);
v_binderType_2199_ = lean_ctor_get(v_e_2191_, 1);
lean_inc_ref(v_binderType_2199_);
v_body_2200_ = lean_ctor_get(v_e_2191_, 2);
lean_inc_ref(v_body_2200_);
v_binderInfo_2201_ = lean_ctor_get_uint8(v_e_2191_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2191_, 3);
v___x_2202_ = lean_expr_instantiate_rev(v_binderType_2199_, v_fvars_2190_);
lean_dec_ref(v_binderType_2199_);
lean_inc_ref(v_post_2186_);
lean_inc_ref(v_pre_2185_);
v___x_2203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2185_, v_post_2186_, v_usedLetOnly_2187_, v_skipConstInApp_2188_, v_skipInstances_2189_, v___x_2202_, v_a_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___f_2208_; uint8_t v___x_2209_; lean_object* v___x_2210_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2205_ = lean_box(v_usedLetOnly_2187_);
v___x_2206_ = lean_box(v_skipConstInApp_2188_);
v___x_2207_ = lean_box(v_skipInstances_2189_);
v___f_2208_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2208_, 0, v_fvars_2190_);
lean_closure_set(v___f_2208_, 1, v_pre_2185_);
lean_closure_set(v___f_2208_, 2, v_post_2186_);
lean_closure_set(v___f_2208_, 3, v___x_2205_);
lean_closure_set(v___f_2208_, 4, v___x_2206_);
lean_closure_set(v___f_2208_, 5, v___x_2207_);
lean_closure_set(v___f_2208_, 6, v_body_2200_);
v___x_2209_ = 0;
v___x_2210_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2198_, v_binderInfo_2201_, v_a_2204_, v___f_2208_, v___x_2209_, v_a_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
return v___x_2210_;
}
else
{
lean_dec_ref(v_body_2200_);
lean_dec(v_binderName_2198_);
lean_dec_ref(v_fvars_2190_);
lean_dec_ref(v_post_2186_);
lean_dec_ref(v_pre_2185_);
return v___x_2203_;
}
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_expr_instantiate_rev(v_e_2191_, v_fvars_2190_);
lean_dec_ref(v_e_2191_);
lean_inc_ref(v_post_2186_);
lean_inc_ref(v_pre_2185_);
v___x_2212_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2185_, v_post_2186_, v_usedLetOnly_2187_, v_skipConstInApp_2188_, v_skipInstances_2189_, v___x_2211_, v_a_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; uint8_t v___x_2214_; uint8_t v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2214_ = 0;
v___x_2215_ = 1;
v___x_2216_ = 1;
v___x_2217_ = l_Lean_Meta_mkForallFVars(v_fvars_2190_, v_a_2213_, v___x_2214_, v_usedLetOnly_2187_, v___x_2215_, v___x_2216_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec_ref(v_fvars_2190_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2185_, v_post_2186_, v_usedLetOnly_2187_, v_skipConstInApp_2188_, v_skipInstances_2189_, v_a_2218_, v_a_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
return v___x_2219_;
}
else
{
lean_dec_ref(v_post_2186_);
lean_dec_ref(v_pre_2185_);
return v___x_2217_;
}
}
else
{
lean_dec_ref(v_fvars_2190_);
lean_dec_ref(v_post_2186_);
lean_dec_ref(v_pre_2185_);
return v___x_2212_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2220_, lean_object* v_pre_2221_, lean_object* v_post_2222_, uint8_t v_usedLetOnly_2223_, uint8_t v_skipConstInApp_2224_, uint8_t v_skipInstances_2225_, lean_object* v_body_2226_, lean_object* v_x_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = lean_array_push(v_fvars_2220_, v_x_2227_);
v___x_2235_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2221_, v_post_2222_, v_usedLetOnly_2223_, v_skipConstInApp_2224_, v_skipInstances_2225_, v___x_2234_, v_body_2226_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2236_, lean_object* v_post_2237_, lean_object* v_usedLetOnly_2238_, lean_object* v_skipConstInApp_2239_, lean_object* v_skipInstances_2240_, lean_object* v_e_2241_, lean_object* v_a_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
uint8_t v_usedLetOnly_boxed_2248_; uint8_t v_skipConstInApp_boxed_2249_; uint8_t v_skipInstances_boxed_2250_; lean_object* v_res_2251_; 
v_usedLetOnly_boxed_2248_ = lean_unbox(v_usedLetOnly_2238_);
v_skipConstInApp_boxed_2249_ = lean_unbox(v_skipConstInApp_2239_);
v_skipInstances_boxed_2250_ = lean_unbox(v_skipInstances_2240_);
v_res_2251_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2236_, v_post_2237_, v_usedLetOnly_boxed_2248_, v_skipConstInApp_boxed_2249_, v_skipInstances_boxed_2250_, v_e_2241_, v_a_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v_a_2242_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_pre_2252_, lean_object* v_post_2253_, lean_object* v_usedLetOnly_2254_, lean_object* v_skipConstInApp_2255_, lean_object* v_skipInstances_2256_, lean_object* v_sz_2257_, lean_object* v_i_2258_, lean_object* v_bs_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
uint8_t v_usedLetOnly_boxed_2266_; uint8_t v_skipConstInApp_boxed_2267_; uint8_t v_skipInstances_boxed_2268_; size_t v_sz_boxed_2269_; size_t v_i_boxed_2270_; lean_object* v_res_2271_; 
v_usedLetOnly_boxed_2266_ = lean_unbox(v_usedLetOnly_2254_);
v_skipConstInApp_boxed_2267_ = lean_unbox(v_skipConstInApp_2255_);
v_skipInstances_boxed_2268_ = lean_unbox(v_skipInstances_2256_);
v_sz_boxed_2269_ = lean_unbox_usize(v_sz_2257_);
lean_dec(v_sz_2257_);
v_i_boxed_2270_ = lean_unbox_usize(v_i_2258_);
lean_dec(v_i_2258_);
v_res_2271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_2252_, v_post_2253_, v_usedLetOnly_boxed_2266_, v_skipConstInApp_boxed_2267_, v_skipInstances_boxed_2268_, v_sz_boxed_2269_, v_i_boxed_2270_, v_bs_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2272_, lean_object* v_post_2273_, lean_object* v_usedLetOnly_2274_, lean_object* v_skipConstInApp_2275_, lean_object* v_skipInstances_2276_, lean_object* v_e_2277_, lean_object* v_a_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
uint8_t v_usedLetOnly_boxed_2284_; uint8_t v_skipConstInApp_boxed_2285_; uint8_t v_skipInstances_boxed_2286_; lean_object* v_res_2287_; 
v_usedLetOnly_boxed_2284_ = lean_unbox(v_usedLetOnly_2274_);
v_skipConstInApp_boxed_2285_ = lean_unbox(v_skipConstInApp_2275_);
v_skipInstances_boxed_2286_ = lean_unbox(v_skipInstances_2276_);
v_res_2287_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2272_, v_post_2273_, v_usedLetOnly_boxed_2284_, v_skipConstInApp_boxed_2285_, v_skipInstances_boxed_2286_, v_e_2277_, v_a_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v_a_2278_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2288_, lean_object* v_post_2289_, lean_object* v_usedLetOnly_2290_, lean_object* v_skipConstInApp_2291_, lean_object* v_skipInstances_2292_, lean_object* v_fvars_2293_, lean_object* v_e_2294_, lean_object* v_a_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
uint8_t v_usedLetOnly_boxed_2301_; uint8_t v_skipConstInApp_boxed_2302_; uint8_t v_skipInstances_boxed_2303_; lean_object* v_res_2304_; 
v_usedLetOnly_boxed_2301_ = lean_unbox(v_usedLetOnly_2290_);
v_skipConstInApp_boxed_2302_ = lean_unbox(v_skipConstInApp_2291_);
v_skipInstances_boxed_2303_ = lean_unbox(v_skipInstances_2292_);
v_res_2304_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2288_, v_post_2289_, v_usedLetOnly_boxed_2301_, v_skipConstInApp_boxed_2302_, v_skipInstances_boxed_2303_, v_fvars_2293_, v_e_2294_, v_a_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v_a_2295_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2305_, lean_object* v_post_2306_, lean_object* v_usedLetOnly_2307_, lean_object* v_skipConstInApp_2308_, lean_object* v_skipInstances_2309_, lean_object* v_fvars_2310_, lean_object* v_e_2311_, lean_object* v_a_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
uint8_t v_usedLetOnly_boxed_2318_; uint8_t v_skipConstInApp_boxed_2319_; uint8_t v_skipInstances_boxed_2320_; lean_object* v_res_2321_; 
v_usedLetOnly_boxed_2318_ = lean_unbox(v_usedLetOnly_2307_);
v_skipConstInApp_boxed_2319_ = lean_unbox(v_skipConstInApp_2308_);
v_skipInstances_boxed_2320_ = lean_unbox(v_skipInstances_2309_);
v_res_2321_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2305_, v_post_2306_, v_usedLetOnly_boxed_2318_, v_skipConstInApp_boxed_2319_, v_skipInstances_boxed_2320_, v_fvars_2310_, v_e_2311_, v_a_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v_a_2312_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2322_, lean_object* v_post_2323_, lean_object* v_usedLetOnly_2324_, lean_object* v_skipConstInApp_2325_, lean_object* v_skipInstances_2326_, lean_object* v_fvars_2327_, lean_object* v_e_2328_, lean_object* v_a_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
uint8_t v_usedLetOnly_boxed_2335_; uint8_t v_skipConstInApp_boxed_2336_; uint8_t v_skipInstances_boxed_2337_; lean_object* v_res_2338_; 
v_usedLetOnly_boxed_2335_ = lean_unbox(v_usedLetOnly_2324_);
v_skipConstInApp_boxed_2336_ = lean_unbox(v_skipConstInApp_2325_);
v_skipInstances_boxed_2337_ = lean_unbox(v_skipInstances_2326_);
v_res_2338_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2322_, v_post_2323_, v_usedLetOnly_boxed_2335_, v_skipConstInApp_boxed_2336_, v_skipInstances_boxed_2337_, v_fvars_2327_, v_e_2328_, v_a_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v_a_2329_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object* v_upperBound_2339_, lean_object* v___x_2340_, lean_object* v_pre_2341_, lean_object* v_post_2342_, lean_object* v_usedLetOnly_2343_, lean_object* v_skipConstInApp_2344_, lean_object* v_skipInstances_2345_, lean_object* v_a_2346_, lean_object* v_b_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
uint8_t v_usedLetOnly_boxed_2354_; uint8_t v_skipConstInApp_boxed_2355_; uint8_t v_skipInstances_boxed_2356_; lean_object* v_res_2357_; 
v_usedLetOnly_boxed_2354_ = lean_unbox(v_usedLetOnly_2343_);
v_skipConstInApp_boxed_2355_ = lean_unbox(v_skipConstInApp_2344_);
v_skipInstances_boxed_2356_ = lean_unbox(v_skipInstances_2345_);
v_res_2357_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_2339_, v___x_2340_, v_pre_2341_, v_post_2342_, v_usedLetOnly_boxed_2354_, v_skipConstInApp_boxed_2355_, v_skipInstances_boxed_2356_, v_a_2346_, v_b_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___x_2340_);
lean_dec(v_upperBound_2339_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2358_, lean_object* v_pre_2359_, lean_object* v_post_2360_, lean_object* v_usedLetOnly_2361_, lean_object* v_skipConstInApp_2362_, lean_object* v_x_2363_, lean_object* v_x_2364_, lean_object* v_x_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
uint8_t v_skipInstances_boxed_2372_; uint8_t v_usedLetOnly_boxed_2373_; uint8_t v_skipConstInApp_boxed_2374_; lean_object* v_res_2375_; 
v_skipInstances_boxed_2372_ = lean_unbox(v_skipInstances_2358_);
v_usedLetOnly_boxed_2373_ = lean_unbox(v_usedLetOnly_2361_);
v_skipConstInApp_boxed_2374_ = lean_unbox(v_skipConstInApp_2362_);
v_res_2375_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2372_, v_pre_2359_, v_post_2360_, v_usedLetOnly_boxed_2373_, v_skipConstInApp_boxed_2374_, v_x_2363_, v_x_2364_, v_x_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
return v_res_2375_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0(void){
_start:
{
lean_object* v_cellCount_2376_; lean_object* v___x_2377_; 
v_cellCount_2376_ = lean_unsigned_to_nat(16u);
v___x_2377_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2376_);
return v___x_2377_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__1(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2378_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2379_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1);
v___x_2380_ = lean_unsigned_to_nat(0u);
v___x_2381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
lean_ctor_set(v___x_2381_, 1, v___x_2379_);
lean_ctor_set(v___x_2381_, 2, v___x_2378_);
return v___x_2381_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__2(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__1);
v___x_2383_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2383_, 0, lean_box(0));
lean_closure_set(v___x_2383_, 1, lean_box(0));
lean_closure_set(v___x_2383_, 2, v___x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2384_, lean_object* v_pre_2385_, lean_object* v_post_2386_, uint8_t v_usedLetOnly_2387_, uint8_t v_skipConstInApp_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v_a_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; 
v___x_2394_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__2);
v___x_2395_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2394_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref(v___x_2395_);
v___x_2397_ = 0;
v___x_2398_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2385_, v_post_2386_, v_usedLetOnly_2387_, v_skipConstInApp_2388_, v___x_2397_, v_input_2384_, v_a_2396_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v___x_2400_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2400_, 0, lean_box(0));
lean_closure_set(v___x_2400_, 1, lean_box(0));
lean_closure_set(v___x_2400_, 2, v_a_2396_);
v___x_2401_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2400_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2408_ == 0)
{
lean_object* v_unused_2409_; 
v_unused_2409_ = lean_ctor_get(v___x_2401_, 0);
lean_dec(v_unused_2409_);
v___x_2403_ = v___x_2401_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_dec(v___x_2401_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v_a_2399_);
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2399_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
else
{
lean_dec(v_a_2396_);
return v___x_2398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2410_, lean_object* v_pre_2411_, lean_object* v_post_2412_, lean_object* v_usedLetOnly_2413_, lean_object* v_skipConstInApp_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
uint8_t v_usedLetOnly_boxed_2420_; uint8_t v_skipConstInApp_boxed_2421_; lean_object* v_res_2422_; 
v_usedLetOnly_boxed_2420_ = lean_unbox(v_usedLetOnly_2413_);
v_skipConstInApp_boxed_2421_ = lean_unbox(v_skipConstInApp_2414_);
v_res_2422_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2410_, v_pre_2411_, v_post_2412_, v_usedLetOnly_boxed_2420_, v_skipConstInApp_boxed_2421_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v___x_2423_, lean_object* v_as_2424_, lean_object* v_j_2425_){
_start:
{
lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2426_ = lean_array_get_size(v_as_2424_);
v___x_2427_ = lean_nat_dec_lt(v_j_2425_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; 
lean_dec(v_j_2425_);
v___x_2428_ = lean_box(0);
return v___x_2428_;
}
else
{
lean_object* v___x_2429_; lean_object* v_declName_2430_; uint8_t v___x_2431_; 
v___x_2429_ = lean_array_fget_borrowed(v_as_2424_, v_j_2425_);
v_declName_2430_ = lean_ctor_get(v___x_2429_, 3);
v___x_2431_ = lean_name_eq(v_declName_2430_, v___x_2423_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = lean_unsigned_to_nat(1u);
v___x_2433_ = lean_nat_add(v_j_2425_, v___x_2432_);
lean_dec(v_j_2425_);
v_j_2425_ = v___x_2433_;
goto _start;
}
else
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2435_, 0, v_j_2425_);
return v___x_2435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v___x_2436_, lean_object* v_as_2437_, lean_object* v_j_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2436_, v_as_2437_, v_j_2438_);
lean_dec_ref(v_as_2437_);
lean_dec(v___x_2436_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_st_ref_get(v_val_2440_);
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object* v_val_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v_val_2448_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2455_, lean_object* v_val_2456_, lean_object* v_a_2457_, lean_object* v___x_2458_, lean_object* v_____r_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2465_ = lean_st_ref_take(v_val_2455_);
v___x_2466_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2456_, v_a_2457_, v___x_2465_);
v___x_2467_ = lean_st_ref_put(v_val_2455_, v___x_2466_);
v___x_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2458_);
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2470_, lean_object* v_val_2471_, lean_object* v_a_2472_, lean_object* v___x_2473_, lean_object* v_____r_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2470_, v_val_2471_, v_a_2472_, v___x_2473_, v_____r_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v_val_2471_);
lean_dec(v_val_2470_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_upperBound_2481_, lean_object* v_val_2482_, lean_object* v_next_2483_, lean_object* v_params_2484_, lean_object* v___x_2485_, lean_object* v_val_2486_, lean_object* v_next_2487_, uint8_t v___x_2488_, lean_object* v_a_2489_, uint8_t v_b_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
uint8_t v_a_2497_; uint8_t v___x_2501_; 
v___x_2501_ = lean_nat_dec_lt(v_a_2489_, v_upperBound_2481_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_dec(v_a_2489_);
lean_dec(v_next_2487_);
lean_dec_ref(v___x_2485_);
v___x_2502_ = lean_box(v_b_2490_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
else
{
lean_object* v___x_2504_; uint8_t v___x_2505_; 
v___x_2504_ = lean_st_ref_get(v_val_2482_);
v___x_2505_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2483_, v_a_2489_, v___x_2504_);
lean_dec(v___x_2504_);
if (v___x_2505_ == 0)
{
v_a_2497_ = v_b_2490_;
goto v___jp_2496_;
}
else
{
lean_object* v___x_2506_; uint8_t v_foApprox_2507_; uint8_t v_ctxApprox_2508_; uint8_t v_quasiPatternApprox_2509_; uint8_t v_constApprox_2510_; uint8_t v_isDefEqStuckEx_2511_; uint8_t v_unificationHints_2512_; uint8_t v_assignSyntheticOpaque_2513_; uint8_t v_offsetCnstrs_2514_; uint8_t v_transparency_2515_; uint8_t v_etaStruct_2516_; uint8_t v_univApprox_2517_; uint8_t v_iota_2518_; uint8_t v_beta_2519_; uint8_t v_proj_2520_; uint8_t v_zeta_2521_; uint8_t v_zetaDelta_2522_; uint8_t v_zetaUnused_2523_; uint8_t v_zetaHave_2524_; uint8_t v_canUnfoldPredicateConfig_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2555_; 
v___x_2506_ = l_Lean_Meta_Context_config(v___y_2491_);
v_foApprox_2507_ = lean_ctor_get_uint8(v___x_2506_, 0);
v_ctxApprox_2508_ = lean_ctor_get_uint8(v___x_2506_, 1);
v_quasiPatternApprox_2509_ = lean_ctor_get_uint8(v___x_2506_, 2);
v_constApprox_2510_ = lean_ctor_get_uint8(v___x_2506_, 3);
v_isDefEqStuckEx_2511_ = lean_ctor_get_uint8(v___x_2506_, 4);
v_unificationHints_2512_ = lean_ctor_get_uint8(v___x_2506_, 5);
v_assignSyntheticOpaque_2513_ = lean_ctor_get_uint8(v___x_2506_, 7);
v_offsetCnstrs_2514_ = lean_ctor_get_uint8(v___x_2506_, 8);
v_transparency_2515_ = lean_ctor_get_uint8(v___x_2506_, 9);
v_etaStruct_2516_ = lean_ctor_get_uint8(v___x_2506_, 10);
v_univApprox_2517_ = lean_ctor_get_uint8(v___x_2506_, 11);
v_iota_2518_ = lean_ctor_get_uint8(v___x_2506_, 12);
v_beta_2519_ = lean_ctor_get_uint8(v___x_2506_, 13);
v_proj_2520_ = lean_ctor_get_uint8(v___x_2506_, 14);
v_zeta_2521_ = lean_ctor_get_uint8(v___x_2506_, 15);
v_zetaDelta_2522_ = lean_ctor_get_uint8(v___x_2506_, 16);
v_zetaUnused_2523_ = lean_ctor_get_uint8(v___x_2506_, 17);
v_zetaHave_2524_ = lean_ctor_get_uint8(v___x_2506_, 18);
v_canUnfoldPredicateConfig_2525_ = lean_ctor_get_uint8(v___x_2506_, 19);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2527_ = v___x_2506_;
v_isShared_2528_ = v_isSharedCheck_2555_;
goto v_resetjp_2526_;
}
else
{
lean_dec(v___x_2506_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2555_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
uint8_t v_trackZetaDelta_2529_; lean_object* v_zetaDeltaSet_2530_; lean_object* v_lctx_2531_; lean_object* v_localInstances_2532_; lean_object* v_defEqCtx_x3f_2533_; lean_object* v_synthPendingDepth_2534_; lean_object* v_customCanUnfoldPredicate_x3f_2535_; uint8_t v_univApprox_2536_; uint8_t v_inTypeClassResolution_2537_; uint8_t v_cacheInferType_2538_; uint8_t v___x_2539_; lean_object* v___x_2541_; 
v_trackZetaDelta_2529_ = lean_ctor_get_uint8(v___y_2491_, sizeof(void*)*7);
v_zetaDeltaSet_2530_ = lean_ctor_get(v___y_2491_, 1);
v_lctx_2531_ = lean_ctor_get(v___y_2491_, 2);
v_localInstances_2532_ = lean_ctor_get(v___y_2491_, 3);
v_defEqCtx_x3f_2533_ = lean_ctor_get(v___y_2491_, 4);
v_synthPendingDepth_2534_ = lean_ctor_get(v___y_2491_, 5);
v_customCanUnfoldPredicate_x3f_2535_ = lean_ctor_get(v___y_2491_, 6);
v_univApprox_2536_ = lean_ctor_get_uint8(v___y_2491_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2537_ = lean_ctor_get_uint8(v___y_2491_, sizeof(void*)*7 + 2);
v_cacheInferType_2538_ = lean_ctor_get_uint8(v___y_2491_, sizeof(void*)*7 + 3);
v___x_2539_ = 0;
if (v_isShared_2528_ == 0)
{
v___x_2541_ = v___x_2527_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 0, v_foApprox_2507_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 1, v_ctxApprox_2508_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 2, v_quasiPatternApprox_2509_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 3, v_constApprox_2510_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 4, v_isDefEqStuckEx_2511_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 5, v_unificationHints_2512_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 7, v_assignSyntheticOpaque_2513_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 8, v_offsetCnstrs_2514_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 9, v_transparency_2515_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 10, v_etaStruct_2516_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 11, v_univApprox_2517_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 12, v_iota_2518_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 13, v_beta_2519_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 14, v_proj_2520_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 15, v_zeta_2521_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 16, v_zetaDelta_2522_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 17, v_zetaUnused_2523_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 18, v_zetaHave_2524_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, 19, v_canUnfoldPredicateConfig_2525_);
v___x_2541_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
uint64_t v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_ctor_set_uint8(v___x_2541_, 6, v___x_2539_);
v___x_2542_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2541_);
v___x_2543_ = lean_array_fget_borrowed(v_params_2484_, v_a_2489_);
v___x_2544_ = 2;
v___x_2545_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2545_, 0, v___x_2541_);
lean_ctor_set_uint64(v___x_2545_, sizeof(void*)*1, v___x_2542_);
v___x_2546_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2544_, v___x_2545_);
lean_inc(v_customCanUnfoldPredicate_x3f_2535_);
lean_inc(v_synthPendingDepth_2534_);
lean_inc(v_defEqCtx_x3f_2533_);
lean_inc_ref(v_localInstances_2532_);
lean_inc_ref(v_lctx_2531_);
lean_inc(v_zetaDeltaSet_2530_);
v___x_2547_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
lean_ctor_set(v___x_2547_, 1, v_zetaDeltaSet_2530_);
lean_ctor_set(v___x_2547_, 2, v_lctx_2531_);
lean_ctor_set(v___x_2547_, 3, v_localInstances_2532_);
lean_ctor_set(v___x_2547_, 4, v_defEqCtx_x3f_2533_);
lean_ctor_set(v___x_2547_, 5, v_synthPendingDepth_2534_);
lean_ctor_set(v___x_2547_, 6, v_customCanUnfoldPredicate_x3f_2535_);
lean_ctor_set_uint8(v___x_2547_, sizeof(void*)*7, v_trackZetaDelta_2529_);
lean_ctor_set_uint8(v___x_2547_, sizeof(void*)*7 + 1, v_univApprox_2536_);
lean_ctor_set_uint8(v___x_2547_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2537_);
lean_ctor_set_uint8(v___x_2547_, sizeof(void*)*7 + 3, v_cacheInferType_2538_);
lean_inc_ref(v___x_2485_);
lean_inc(v___x_2543_);
v___x_2548_ = l_Lean_Meta_isExprDefEq(v___x_2543_, v___x_2485_, v___x_2547_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec_ref_known(v___x_2547_, 7);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; uint8_t v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v___x_2550_ = lean_unbox(v_a_2549_);
lean_dec(v_a_2549_);
if (v___x_2550_ == 0)
{
v_a_2497_ = v_b_2490_;
goto v___jp_2496_;
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2551_ = lean_st_ref_take(v_val_2482_);
lean_inc(v_a_2489_);
lean_inc(v_next_2487_);
v___x_2552_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2486_, v_next_2487_, v_next_2483_, v_a_2489_, v___x_2551_);
v___x_2553_ = lean_st_ref_put(v_val_2482_, v___x_2552_);
v_a_2497_ = v___x_2488_;
goto v___jp_2496_;
}
}
else
{
lean_dec(v_a_2489_);
lean_dec(v_next_2487_);
lean_dec_ref(v___x_2485_);
return v___x_2548_;
}
}
}
}
}
v___jp_2496_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = lean_unsigned_to_nat(1u);
v___x_2499_ = lean_nat_add(v_a_2489_, v___x_2498_);
lean_dec(v_a_2489_);
v_a_2489_ = v___x_2499_;
v_b_2490_ = v_a_2497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_upperBound_2556_, lean_object* v_val_2557_, lean_object* v_next_2558_, lean_object* v_params_2559_, lean_object* v___x_2560_, lean_object* v_val_2561_, lean_object* v_next_2562_, lean_object* v___x_2563_, lean_object* v_a_2564_, lean_object* v_b_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
uint8_t v___x_43721__boxed_2571_; uint8_t v_b_boxed_2572_; lean_object* v_res_2573_; 
v___x_43721__boxed_2571_ = lean_unbox(v___x_2563_);
v_b_boxed_2572_ = lean_unbox(v_b_2565_);
v_res_2573_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_2556_, v_val_2557_, v_next_2558_, v_params_2559_, v___x_2560_, v_val_2561_, v_next_2562_, v___x_43721__boxed_2571_, v_a_2564_, v_b_boxed_2572_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v_val_2561_);
lean_dec_ref(v_params_2559_);
lean_dec(v_next_2558_);
lean_dec(v_val_2557_);
lean_dec(v_upperBound_2556_);
return v_res_2573_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2585_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2586_ = l_Lean_Name_append(v___x_2585_, v___x_2584_);
return v___x_2586_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2589_ = l_Lean_stringToMessageData(v___x_2588_);
return v___x_2589_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2591_ = l_Lean_stringToMessageData(v___x_2590_);
return v___x_2591_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2594_ = l_Lean_stringToMessageData(v___x_2593_);
return v___x_2594_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2597_ = l_Lean_stringToMessageData(v___x_2596_);
return v___x_2597_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2600_ = l_Lean_stringToMessageData(v___x_2599_);
return v___x_2600_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2603_ = l_Lean_stringToMessageData(v___x_2602_);
return v___x_2603_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
v___x_2606_ = l_Lean_stringToMessageData(v___x_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2607_, lean_object* v_val_2608_, lean_object* v_upperBound_2609_, lean_object* v_args_2610_, lean_object* v_e_2611_, lean_object* v_next_2612_, lean_object* v_params_2613_, lean_object* v___x_2614_, uint8_t v___x_2615_, lean_object* v_a_2616_, lean_object* v_b_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_a_2624_; lean_object* v___y_2629_; uint8_t v___x_2648_; 
v___x_2648_ = lean_nat_dec_lt(v_a_2616_, v_upperBound_2609_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; 
lean_dec(v_a_2616_);
lean_dec_ref(v_e_2611_);
lean_dec(v_val_2608_);
v___x_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_b_2617_);
return v___x_2649_;
}
else
{
lean_object* v___x_2650_; 
v___x_2650_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2607_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v___x_2652_ = lean_box(0);
v___x_2653_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2608_, v_a_2616_, v_a_2651_);
lean_dec(v_a_2651_);
if (v___x_2653_ == 0)
{
v_a_2624_ = v___x_2652_;
goto v___jp_2623_;
}
else
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = lean_array_get_size(v_args_2610_);
v___x_2655_ = lean_nat_dec_lt(v_a_2616_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v_options_2656_; lean_object* v_inheritedTraceOptions_2657_; uint8_t v_hasTrace_2658_; 
v_options_2656_ = lean_ctor_get(v___y_2620_, 2);
v_inheritedTraceOptions_2657_ = lean_ctor_get(v___y_2620_, 13);
v_hasTrace_2658_ = lean_ctor_get_uint8(v_options_2656_, sizeof(void*)*1);
if (v_hasTrace_2658_ == 0)
{
goto v___jp_2659_;
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2661_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2662_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2663_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2657_, v_options_2656_, v___x_2662_);
if (v___x_2663_ == 0)
{
goto v___jp_2659_;
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2664_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2608_);
v___x_2665_ = l_Nat_reprFast(v_val_2608_);
v___x_2666_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
v___x_2667_ = l_Lean_MessageData_ofFormat(v___x_2666_);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2664_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
lean_inc(v_a_2616_);
v___x_2671_ = l_Nat_reprFast(v_a_2616_);
v___x_2672_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
v___x_2673_ = l_Lean_MessageData_ofFormat(v___x_2672_);
lean_inc_ref(v___x_2673_);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2670_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
lean_inc_ref(v_e_2611_);
v___x_2677_ = l_Lean_MessageData_ofExpr(v_e_2611_);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2678_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
lean_ctor_set(v___x_2681_, 1, v___x_2673_);
v___x_2682_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2661_, v___x_2681_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
lean_inc(v_a_2616_);
v___x_2684_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2607_, v_val_2608_, v_a_2616_, v___x_2652_, v_a_2683_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
v___y_2629_ = v___x_2684_;
goto v___jp_2628_;
}
else
{
lean_dec(v_a_2616_);
lean_dec_ref(v_e_2611_);
lean_dec(v_val_2608_);
return v___x_2682_;
}
}
}
v___jp_2659_:
{
lean_object* v___x_2660_; 
lean_inc(v_a_2616_);
v___x_2660_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2607_, v_val_2608_, v_a_2616_, v___x_2652_, v___x_2652_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
v___y_2629_ = v___x_2660_;
goto v___jp_2628_;
}
}
else
{
lean_object* v___x_2685_; 
v___x_2685_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2607_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2687_ = lean_array_fget_borrowed(v_args_2610_, v_a_2616_);
v___x_2688_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2608_, v_a_2616_, v_next_2612_, v_a_2686_);
lean_dec(v_a_2686_);
if (lean_obj_tag(v___x_2688_) == 1)
{
lean_object* v_val_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2785_; 
v_val_2689_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2691_ = v___x_2688_;
v_isShared_2692_ = v_isSharedCheck_2785_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_val_2689_);
lean_dec(v___x_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2785_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; uint8_t v_foApprox_2694_; uint8_t v_ctxApprox_2695_; uint8_t v_quasiPatternApprox_2696_; uint8_t v_constApprox_2697_; uint8_t v_isDefEqStuckEx_2698_; uint8_t v_unificationHints_2699_; uint8_t v_assignSyntheticOpaque_2700_; uint8_t v_offsetCnstrs_2701_; uint8_t v_transparency_2702_; uint8_t v_etaStruct_2703_; uint8_t v_univApprox_2704_; uint8_t v_iota_2705_; uint8_t v_beta_2706_; uint8_t v_proj_2707_; uint8_t v_zeta_2708_; uint8_t v_zetaDelta_2709_; uint8_t v_zetaUnused_2710_; uint8_t v_zetaHave_2711_; uint8_t v_canUnfoldPredicateConfig_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2784_; 
v___x_2693_ = l_Lean_Meta_Context_config(v___y_2618_);
v_foApprox_2694_ = lean_ctor_get_uint8(v___x_2693_, 0);
v_ctxApprox_2695_ = lean_ctor_get_uint8(v___x_2693_, 1);
v_quasiPatternApprox_2696_ = lean_ctor_get_uint8(v___x_2693_, 2);
v_constApprox_2697_ = lean_ctor_get_uint8(v___x_2693_, 3);
v_isDefEqStuckEx_2698_ = lean_ctor_get_uint8(v___x_2693_, 4);
v_unificationHints_2699_ = lean_ctor_get_uint8(v___x_2693_, 5);
v_assignSyntheticOpaque_2700_ = lean_ctor_get_uint8(v___x_2693_, 7);
v_offsetCnstrs_2701_ = lean_ctor_get_uint8(v___x_2693_, 8);
v_transparency_2702_ = lean_ctor_get_uint8(v___x_2693_, 9);
v_etaStruct_2703_ = lean_ctor_get_uint8(v___x_2693_, 10);
v_univApprox_2704_ = lean_ctor_get_uint8(v___x_2693_, 11);
v_iota_2705_ = lean_ctor_get_uint8(v___x_2693_, 12);
v_beta_2706_ = lean_ctor_get_uint8(v___x_2693_, 13);
v_proj_2707_ = lean_ctor_get_uint8(v___x_2693_, 14);
v_zeta_2708_ = lean_ctor_get_uint8(v___x_2693_, 15);
v_zetaDelta_2709_ = lean_ctor_get_uint8(v___x_2693_, 16);
v_zetaUnused_2710_ = lean_ctor_get_uint8(v___x_2693_, 17);
v_zetaHave_2711_ = lean_ctor_get_uint8(v___x_2693_, 18);
v_canUnfoldPredicateConfig_2712_ = lean_ctor_get_uint8(v___x_2693_, 19);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2714_ = v___x_2693_;
v_isShared_2715_ = v_isSharedCheck_2784_;
goto v_resetjp_2713_;
}
else
{
lean_dec(v___x_2693_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2784_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
uint8_t v_trackZetaDelta_2716_; lean_object* v_zetaDeltaSet_2717_; lean_object* v_lctx_2718_; lean_object* v_localInstances_2719_; lean_object* v_defEqCtx_x3f_2720_; lean_object* v_synthPendingDepth_2721_; lean_object* v_customCanUnfoldPredicate_x3f_2722_; uint8_t v_univApprox_2723_; uint8_t v_inTypeClassResolution_2724_; uint8_t v_cacheInferType_2725_; uint8_t v___x_2726_; lean_object* v___x_2728_; 
v_trackZetaDelta_2716_ = lean_ctor_get_uint8(v___y_2618_, sizeof(void*)*7);
v_zetaDeltaSet_2717_ = lean_ctor_get(v___y_2618_, 1);
v_lctx_2718_ = lean_ctor_get(v___y_2618_, 2);
v_localInstances_2719_ = lean_ctor_get(v___y_2618_, 3);
v_defEqCtx_x3f_2720_ = lean_ctor_get(v___y_2618_, 4);
v_synthPendingDepth_2721_ = lean_ctor_get(v___y_2618_, 5);
v_customCanUnfoldPredicate_x3f_2722_ = lean_ctor_get(v___y_2618_, 6);
v_univApprox_2723_ = lean_ctor_get_uint8(v___y_2618_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2724_ = lean_ctor_get_uint8(v___y_2618_, sizeof(void*)*7 + 2);
v_cacheInferType_2725_ = lean_ctor_get_uint8(v___y_2618_, sizeof(void*)*7 + 3);
v___x_2726_ = 0;
if (v_isShared_2715_ == 0)
{
v___x_2728_ = v___x_2714_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 0, v_foApprox_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 1, v_ctxApprox_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 2, v_quasiPatternApprox_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 3, v_constApprox_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 4, v_isDefEqStuckEx_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 5, v_unificationHints_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 7, v_assignSyntheticOpaque_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 8, v_offsetCnstrs_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 9, v_transparency_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 10, v_etaStruct_2703_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 11, v_univApprox_2704_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 12, v_iota_2705_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 13, v_beta_2706_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 14, v_proj_2707_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 15, v_zeta_2708_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 16, v_zetaDelta_2709_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 17, v_zetaUnused_2710_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 18, v_zetaHave_2711_);
lean_ctor_set_uint8(v_reuseFailAlloc_2783_, 19, v_canUnfoldPredicateConfig_2712_);
v___x_2728_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
uint64_t v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_ctor_set_uint8(v___x_2728_, 6, v___x_2726_);
v___x_2729_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2728_);
v___x_2730_ = l_Lean_instInhabitedExpr;
v___x_2731_ = lean_array_get_borrowed(v___x_2730_, v_params_2613_, v_val_2689_);
lean_dec(v_val_2689_);
v___x_2732_ = 2;
v___x_2733_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2733_, 0, v___x_2728_);
lean_ctor_set_uint64(v___x_2733_, sizeof(void*)*1, v___x_2729_);
v___x_2734_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2732_, v___x_2733_);
lean_inc(v_customCanUnfoldPredicate_x3f_2722_);
lean_inc(v_synthPendingDepth_2721_);
lean_inc(v_defEqCtx_x3f_2720_);
lean_inc_ref(v_localInstances_2719_);
lean_inc_ref(v_lctx_2718_);
lean_inc(v_zetaDeltaSet_2717_);
v___x_2735_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
lean_ctor_set(v___x_2735_, 1, v_zetaDeltaSet_2717_);
lean_ctor_set(v___x_2735_, 2, v_lctx_2718_);
lean_ctor_set(v___x_2735_, 3, v_localInstances_2719_);
lean_ctor_set(v___x_2735_, 4, v_defEqCtx_x3f_2720_);
lean_ctor_set(v___x_2735_, 5, v_synthPendingDepth_2721_);
lean_ctor_set(v___x_2735_, 6, v_customCanUnfoldPredicate_x3f_2722_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*7, v_trackZetaDelta_2716_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*7 + 1, v_univApprox_2723_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2724_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*7 + 3, v_cacheInferType_2725_);
lean_inc(v___x_2687_);
lean_inc(v___x_2731_);
v___x_2736_ = l_Lean_Meta_isExprDefEq(v___x_2731_, v___x_2687_, v___x_2735_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec_ref_known(v___x_2735_, 7);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; uint8_t v___x_2738_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = lean_unbox(v_a_2737_);
lean_dec(v_a_2737_);
if (v___x_2738_ == 0)
{
lean_object* v_options_2739_; lean_object* v_inheritedTraceOptions_2740_; uint8_t v_hasTrace_2741_; 
v_options_2739_ = lean_ctor_get(v___y_2620_, 2);
v_inheritedTraceOptions_2740_ = lean_ctor_get(v___y_2620_, 13);
v_hasTrace_2741_ = lean_ctor_get_uint8(v_options_2739_, sizeof(void*)*1);
if (v_hasTrace_2741_ == 0)
{
lean_del_object(v___x_2691_);
goto v___jp_2742_;
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; 
v___x_2744_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2745_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2746_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2740_, v_options_2739_, v___x_2745_);
if (v___x_2746_ == 0)
{
lean_del_object(v___x_2691_);
goto v___jp_2742_;
}
else
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2747_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2608_);
v___x_2748_ = l_Nat_reprFast(v_val_2608_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set_tag(v___x_2691_, 3);
lean_ctor_set(v___x_2691_, 0, v___x_2748_);
v___x_2750_ = v___x_2691_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2751_ = l_Lean_MessageData_ofFormat(v___x_2750_);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2747_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
lean_inc(v_a_2616_);
v___x_2755_ = l_Nat_reprFast(v_a_2616_);
v___x_2756_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
v___x_2757_ = l_Lean_MessageData_ofFormat(v___x_2756_);
v___x_2758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2754_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
lean_inc_ref(v_e_2611_);
v___x_2761_ = l_Lean_MessageData_ofExpr(v_e_2611_);
v___x_2762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
lean_inc(v___x_2731_);
v___x_2765_ = l_Lean_MessageData_ofExpr(v___x_2731_);
v___x_2766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
lean_inc(v___x_2687_);
v___x_2769_ = l_Lean_MessageData_ofExpr(v___x_2687_);
v___x_2770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2768_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
v___x_2771_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2744_, v___x_2770_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
lean_inc(v_a_2616_);
v___x_2773_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2607_, v_val_2608_, v_a_2616_, v___x_2652_, v_a_2772_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
v___y_2629_ = v___x_2773_;
goto v___jp_2628_;
}
else
{
lean_dec(v_a_2616_);
lean_dec_ref(v_e_2611_);
lean_dec(v_val_2608_);
return v___x_2771_;
}
}
}
}
v___jp_2742_:
{
lean_object* v___x_2743_; 
lean_inc(v_a_2616_);
v___x_2743_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2607_, v_val_2608_, v_a_2616_, v___x_2652_, v___x_2652_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
v___y_2629_ = v___x_2743_;
goto v___jp_2628_;
}
}
else
{
lean_del_object(v___x_2691_);
v_a_2624_ = v___x_2652_;
goto v___jp_2623_;
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_del_object(v___x_2691_);
lean_dec(v_a_2616_);
lean_dec_ref(v_e_2611_);
lean_dec(v_val_2608_);
v_a_2775_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2736_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2736_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2786_; uint8_t v___x_2787_; lean_object* v___x_2788_; 
lean_dec(v___x_2688_);
v___x_2786_ = lean_unsigned_to_nat(0u);
v___x_2787_ = 0;
lean_inc(v_a_2616_);
lean_inc(v___x_2687_);
v___x_2788_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v___x_2614_, v_val_2607_, v_next_2612_, v_params_2613_, v___x_2687_, v_val_2608_, v_a_2616_, v___x_2615_, v___x_2786_, v___x_2787_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; uint8_t v___x_2790_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2790_ = lean_unbox(v_a_2789_);
lean_dec(v_a_2789_);
if (v___x_2790_ == 0)
{
lean_object* v_options_2791_; lean_object* v_inheritedTraceOptions_2792_; uint8_t v_hasTrace_2793_; 
v_options_2791_ = lean_ctor_get(v___y_2620_, 2);
v_inheritedTraceOptions_2792_ = lean_ctor_get(v___y_2620_, 13);
v_hasTrace_2793_ = lean_ctor_get_uint8(v_options_2791_, sizeof(void*)*1);
if (v_hasTrace_2793_ == 0)
{
goto v___jp_2794_;
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2796_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2797_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2792_, v_options_2791_, v___x_2797_);
if (v___x_2798_ == 0)
{
goto v___jp_2794_;
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2799_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2608_);
v___x_2800_ = l_Nat_reprFast(v_val_2608_);
v___x_2801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
v___x_2802_ = l_Lean_MessageData_ofFormat(v___x_2801_);
v___x_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2799_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
lean_inc(v_a_2616_);
v___x_2806_ = l_Nat_reprFast(v_a_2616_);
v___x_2807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
v___x_2808_ = l_Lean_MessageData_ofFormat(v___x_2807_);
v___x_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2805_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
lean_inc_ref(v_e_2611_);
v___x_2812_ = l_Lean_MessageData_ofExpr(v_e_2611_);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
lean_inc(v___x_2687_);
v___x_2816_ = l_Lean_MessageData_ofExpr(v___x_2687_);
v___x_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2815_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2817_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2796_, v___x_2819_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
lean_inc(v_a_2616_);
v___x_2822_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2607_, v_val_2608_, v_a_2616_, v___x_2652_, v_a_2821_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
v___y_2629_ = v___x_2822_;
goto v___jp_2628_;
}
else
{
lean_dec(v_a_2616_);
lean_dec_ref(v_e_2611_);
lean_dec(v_val_2608_);
return v___x_2820_;
}
}
}
v___jp_2794_:
{
lean_object* v___x_2795_; 
lean_inc(v_a_2616_);
v___x_2795_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2607_, v_val_2608_, v_a_2616_, v___x_2652_, v___x_2652_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
v___y_2629_ = v___x_2795_;
goto v___jp_2628_;
}
}
else
{
v_a_2624_ = v___x_2652_;
goto v___jp_2623_;
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v_a_2616_);
lean_dec_ref(v_e_2611_);
lean_dec(v_val_2608_);
v_a_2823_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2788_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2788_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec(v_a_2616_);
lean_dec_ref(v_e_2611_);
lean_dec(v_val_2608_);
v_a_2831_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2685_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2685_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v_a_2616_);
lean_dec_ref(v_e_2611_);
lean_dec(v_val_2608_);
v_a_2839_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2650_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2650_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
v___jp_2623_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_unsigned_to_nat(1u);
v___x_2626_ = lean_nat_add(v_a_2616_, v___x_2625_);
lean_dec(v_a_2616_);
v_a_2616_ = v___x_2626_;
v_b_2617_ = v_a_2624_;
goto _start;
}
v___jp_2628_:
{
if (lean_obj_tag(v___y_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2639_; 
v_a_2630_ = lean_ctor_get(v___y_2629_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___y_2629_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2632_ = v___y_2629_;
v_isShared_2633_ = v_isSharedCheck_2639_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___y_2629_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2639_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
if (lean_obj_tag(v_a_2630_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2636_; 
lean_dec(v_a_2616_);
lean_dec_ref(v_e_2611_);
lean_dec(v_val_2608_);
v_a_2634_ = lean_ctor_get(v_a_2630_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v_a_2630_, 1);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 0, v_a_2634_);
v___x_2636_ = v___x_2632_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
else
{
lean_object* v_a_2638_; 
lean_del_object(v___x_2632_);
v_a_2638_ = lean_ctor_get(v_a_2630_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v_a_2630_, 1);
v_a_2624_ = v_a_2638_;
goto v___jp_2623_;
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec(v_a_2616_);
lean_dec_ref(v_e_2611_);
lean_dec(v_val_2608_);
v_a_2640_ = lean_ctor_get(v___y_2629_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___y_2629_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___y_2629_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___y_2629_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2847_, lean_object* v_val_2848_, lean_object* v_upperBound_2849_, lean_object* v_args_2850_, lean_object* v_e_2851_, lean_object* v_next_2852_, lean_object* v_params_2853_, lean_object* v___x_2854_, lean_object* v___x_2855_, lean_object* v_a_2856_, lean_object* v_b_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
uint8_t v___x_43928__boxed_2863_; lean_object* v_res_2864_; 
v___x_43928__boxed_2863_ = lean_unbox(v___x_2855_);
v_res_2864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2847_, v_val_2848_, v_upperBound_2849_, v_args_2850_, v_e_2851_, v_next_2852_, v_params_2853_, v___x_2854_, v___x_43928__boxed_2863_, v_a_2856_, v_b_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___x_2854_);
lean_dec_ref(v_params_2853_);
lean_dec(v_next_2852_);
lean_dec_ref(v_args_2850_);
lean_dec(v_upperBound_2849_);
lean_dec(v_val_2847_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2867_, lean_object* v___x_2868_, lean_object* v_val_2869_, lean_object* v_e_2870_, lean_object* v_next_2871_, lean_object* v_params_2872_, lean_object* v___x_2873_, lean_object* v_x_2874_, lean_object* v_x_2875_, lean_object* v_x_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
if (lean_obj_tag(v_x_2874_) == 5)
{
lean_object* v_fn_2882_; lean_object* v_arg_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_fn_2882_ = lean_ctor_get(v_x_2874_, 0);
lean_inc_ref(v_fn_2882_);
v_arg_2883_ = lean_ctor_get(v_x_2874_, 1);
lean_inc_ref(v_arg_2883_);
lean_dec_ref_known(v_x_2874_, 2);
v___x_2884_ = lean_array_set(v_x_2875_, v_x_2876_, v_arg_2883_);
v___x_2885_ = lean_unsigned_to_nat(1u);
v___x_2886_ = lean_nat_sub(v_x_2876_, v___x_2885_);
lean_dec(v_x_2876_);
v_x_2874_ = v_fn_2882_;
v_x_2875_ = v___x_2884_;
v_x_2876_ = v___x_2886_;
goto _start;
}
else
{
uint8_t v___x_2888_; 
lean_dec(v_x_2876_);
v___x_2888_ = l_Lean_Expr_isConst(v_x_2874_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_dec_ref(v_x_2875_);
lean_dec_ref(v_x_2874_);
lean_dec_ref(v_e_2870_);
v___x_2889_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
return v___x_2890_;
}
else
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = l_Lean_Expr_constName_x21(v_x_2874_);
lean_dec_ref(v_x_2874_);
v___x_2892_ = lean_unsigned_to_nat(0u);
v___x_2893_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2891_, v_preDefs_2867_, v___x_2892_);
lean_dec(v___x_2891_);
if (lean_obj_tag(v___x_2893_) == 1)
{
lean_object* v_val_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_val_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_val_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = lean_box(0);
v___x_2896_ = lean_array_get_borrowed(v___x_2892_, v___x_2868_, v_val_2894_);
v___x_2897_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2869_, v_val_2894_, v___x_2896_, v_x_2875_, v_e_2870_, v_next_2871_, v_params_2872_, v___x_2873_, v___x_2888_, v___x_2892_, v___x_2895_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec_ref(v_x_2875_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2905_; 
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2905_ == 0)
{
lean_object* v_unused_2906_; 
v_unused_2906_ = lean_ctor_get(v___x_2897_, 0);
lean_dec(v_unused_2906_);
v___x_2899_ = v___x_2897_;
v_isShared_2900_ = v_isSharedCheck_2905_;
goto v_resetjp_2898_;
}
else
{
lean_dec(v___x_2897_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2905_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2901_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v___x_2901_);
v___x_2903_ = v___x_2899_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
v_a_2907_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2897_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2897_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
lean_dec(v___x_2893_);
lean_dec_ref(v_x_2875_);
lean_dec_ref(v_e_2870_);
v___x_2915_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
return v___x_2916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2917_, lean_object* v___x_2918_, lean_object* v_val_2919_, lean_object* v_e_2920_, lean_object* v_next_2921_, lean_object* v_params_2922_, lean_object* v___x_2923_, lean_object* v_x_2924_, lean_object* v_x_2925_, lean_object* v_x_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2917_, v___x_2918_, v_val_2919_, v_e_2920_, v_next_2921_, v_params_2922_, v___x_2923_, v_x_2924_, v_x_2925_, v_x_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___x_2923_);
lean_dec_ref(v_params_2922_);
lean_dec(v_next_2921_);
lean_dec(v_val_2919_);
lean_dec_ref(v___x_2918_);
lean_dec_ref(v_preDefs_2917_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2933_, lean_object* v___x_2934_, lean_object* v_val_2935_, lean_object* v_a_2936_, lean_object* v_params_2937_, lean_object* v___x_2938_, lean_object* v_e_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v_dummy_2945_; lean_object* v_nargs_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v_dummy_2945_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2946_ = l_Lean_Expr_getAppNumArgs(v_e_2939_);
lean_inc(v_nargs_2946_);
v___x_2947_ = lean_mk_array(v_nargs_2946_, v_dummy_2945_);
v___x_2948_ = lean_unsigned_to_nat(1u);
v___x_2949_ = lean_nat_sub(v_nargs_2946_, v___x_2948_);
lean_dec(v_nargs_2946_);
lean_inc_ref(v_e_2939_);
v___x_2950_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2933_, v___x_2934_, v_val_2935_, v_e_2939_, v_a_2936_, v_params_2937_, v___x_2938_, v_e_2939_, v___x_2947_, v___x_2949_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2951_, lean_object* v___x_2952_, lean_object* v_val_2953_, lean_object* v_a_2954_, lean_object* v_params_2955_, lean_object* v___x_2956_, lean_object* v_e_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2951_, v___x_2952_, v_val_2953_, v_a_2954_, v_params_2955_, v___x_2956_, v_e_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___x_2956_);
lean_dec_ref(v_params_2955_);
lean_dec(v_a_2954_);
lean_dec(v_val_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_preDefs_2951_);
return v_res_2963_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2967_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2968_ = lean_unsigned_to_nat(6u);
v___x_2969_ = lean_unsigned_to_nat(201u);
v___x_2970_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2971_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2972_ = l_mkPanicMessageWithDecl(v___x_2971_, v___x_2970_, v___x_2969_, v___x_2968_, v___x_2967_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2973_, lean_object* v___x_2974_, lean_object* v_a_2975_, lean_object* v_preDefs_2976_, lean_object* v_val_2977_, lean_object* v___f_2978_, lean_object* v___x_2979_, lean_object* v_params_2980_, lean_object* v_body_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; 
v___x_2987_ = lean_array_get_size(v_params_2980_);
v___x_2988_ = lean_array_get_borrowed(v___x_2973_, v___x_2974_, v_a_2975_);
v___x_2989_ = lean_nat_dec_eq(v___x_2987_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
lean_dec_ref(v_body_2981_);
lean_dec_ref(v_params_2980_);
lean_dec_ref(v___f_2978_);
lean_dec(v_val_2977_);
lean_dec_ref(v_preDefs_2976_);
lean_dec(v_a_2975_);
lean_dec_ref(v___x_2974_);
v___x_2990_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2991_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2990_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_2991_;
}
else
{
lean_object* v___f_2992_; uint8_t v___x_2993_; lean_object* v___x_2994_; 
v___f_2992_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_2992_, 0, v_preDefs_2976_);
lean_closure_set(v___f_2992_, 1, v___x_2974_);
lean_closure_set(v___f_2992_, 2, v_val_2977_);
lean_closure_set(v___f_2992_, 3, v_a_2975_);
lean_closure_set(v___f_2992_, 4, v_params_2980_);
lean_closure_set(v___f_2992_, 5, v___x_2987_);
v___x_2993_ = 0;
v___x_2994_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2981_, v___f_2992_, v___f_2978_, v___x_2993_, v___x_2989_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3001_ == 0)
{
lean_object* v_unused_3002_; 
v_unused_3002_ = lean_ctor_get(v___x_2994_, 0);
lean_dec(v_unused_3002_);
v___x_2996_ = v___x_2994_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_dec(v___x_2994_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 0, v___x_2979_);
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2979_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
v_a_3003_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2994_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2994_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_3011_, lean_object* v___x_3012_, lean_object* v_a_3013_, lean_object* v_preDefs_3014_, lean_object* v_val_3015_, lean_object* v___f_3016_, lean_object* v___x_3017_, lean_object* v_params_3018_, lean_object* v_body_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_3011_, v___x_3012_, v_a_3013_, v_preDefs_3014_, v_val_3015_, v___f_3016_, v___x_3017_, v_params_3018_, v_body_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___x_3011_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3032_, 0, v_e_3026_);
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v_preDefs_3042_, lean_object* v___x_3043_, lean_object* v_val_3044_, lean_object* v_upperBound_3045_, lean_object* v_a_3046_, lean_object* v_b_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
uint8_t v___x_3053_; 
v___x_3053_ = lean_nat_dec_lt(v_a_3046_, v_upperBound_3045_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; 
lean_dec(v_a_3046_);
lean_dec(v_val_3044_);
lean_dec_ref(v___x_3043_);
lean_dec_ref(v_preDefs_3042_);
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v_b_3047_);
return v___x_3054_;
}
else
{
lean_object* v___x_3055_; lean_object* v_value_3056_; lean_object* v___f_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___f_3060_; uint8_t v___x_3061_; lean_object* v___x_3062_; 
v___x_3055_ = lean_array_fget_borrowed(v_preDefs_3042_, v_a_3046_);
v_value_3056_ = lean_ctor_get(v___x_3055_, 7);
v___f_3057_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3058_ = lean_unsigned_to_nat(0u);
v___x_3059_ = lean_box(0);
lean_inc(v_val_3044_);
lean_inc_ref(v_preDefs_3042_);
lean_inc(v_a_3046_);
lean_inc_ref(v___x_3043_);
v___f_3060_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3060_, 0, v___x_3058_);
lean_closure_set(v___f_3060_, 1, v___x_3043_);
lean_closure_set(v___f_3060_, 2, v_a_3046_);
lean_closure_set(v___f_3060_, 3, v_preDefs_3042_);
lean_closure_set(v___f_3060_, 4, v_val_3044_);
lean_closure_set(v___f_3060_, 5, v___f_3057_);
lean_closure_set(v___f_3060_, 6, v___x_3059_);
v___x_3061_ = 0;
lean_inc_ref(v_value_3056_);
v___x_3062_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_3056_, v___f_3060_, v___x_3061_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
lean_dec_ref_known(v___x_3062_, 1);
v___x_3063_ = lean_unsigned_to_nat(1u);
v___x_3064_ = lean_nat_add(v_a_3046_, v___x_3063_);
lean_dec(v_a_3046_);
v_a_3046_ = v___x_3064_;
v_b_3047_ = v___x_3059_;
goto _start;
}
else
{
lean_dec(v_a_3046_);
lean_dec(v_val_3044_);
lean_dec_ref(v___x_3043_);
lean_dec_ref(v_preDefs_3042_);
return v___x_3062_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v_preDefs_3066_, lean_object* v___x_3067_, lean_object* v_val_3068_, lean_object* v_upperBound_3069_, lean_object* v_a_3070_, lean_object* v_b_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3066_, v___x_3067_, v_val_3068_, v_upperBound_3069_, v_a_3070_, v_b_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v_upperBound_3069_);
return v_res_3077_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3080_ = l_Lean_stringToMessageData(v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
size_t v_sz_3087_; size_t v___x_3088_; lean_object* v___x_3089_; 
v_sz_3087_ = lean_array_size(v_preDefs_3081_);
v___x_3088_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3081_);
v___x_3089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3087_, v___x_3088_, v_preDefs_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; size_t v_sz_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc_n(v_a_3090_, 2);
lean_dec_ref_known(v___x_3089_, 1);
v_sz_3091_ = lean_array_size(v_a_3090_);
v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3091_, v___x_3088_, v_a_3090_);
v___x_3093_ = l_Lean_Elab_FixedParams_Info_init(v_a_3090_);
v___x_3094_ = lean_st_mk_ref(v___x_3093_);
v___x_3095_ = lean_st_ref_take(v___x_3094_);
v___x_3096_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3095_);
v___x_3097_ = lean_st_ref_put(v___x_3094_, v___x_3096_);
v___x_3098_ = lean_array_get_size(v_preDefs_3081_);
v___x_3099_ = lean_unsigned_to_nat(0u);
v___x_3100_ = lean_box(0);
lean_inc(v___x_3094_);
v___x_3101_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3081_, v___x_3092_, v___x_3094_, v___x_3098_, v___x_3099_, v___x_3100_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3140_; 
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v___x_3101_, 0);
lean_dec(v_unused_3141_);
v___x_3103_ = v___x_3101_;
v_isShared_3104_ = v_isSharedCheck_3140_;
goto v_resetjp_3102_;
}
else
{
lean_dec(v___x_3101_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3140_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3105_; lean_object* v_options_3106_; uint8_t v_hasTrace_3107_; 
v___x_3105_ = lean_st_ref_get(v___x_3094_);
lean_dec(v___x_3094_);
v_options_3106_ = lean_ctor_get(v_a_3084_, 2);
v_hasTrace_3107_ = lean_ctor_get_uint8(v_options_3106_, sizeof(void*)*1);
if (v_hasTrace_3107_ == 0)
{
lean_object* v___x_3109_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3105_);
v___x_3109_ = v___x_3103_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3105_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v_inheritedTraceOptions_3111_ = lean_ctor_get(v_a_3084_, 13);
v___x_3112_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3113_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3114_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3111_, v_options_3106_, v___x_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3116_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3105_);
v___x_3116_ = v___x_3103_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3105_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_del_object(v___x_3103_);
v___x_3118_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3105_);
v___x_3119_ = l_Lean_Elab_FixedParams_Info_format(v___x_3105_);
v___x_3120_ = l_Std_Format_indentD(v___x_3119_);
v___x_3121_ = l_Lean_MessageData_ofFormat(v___x_3120_);
v___x_3122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3118_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
v___x_3123_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3112_, v___x_3122_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; 
v_unused_3131_ = lean_ctor_get(v___x_3123_, 0);
lean_dec(v_unused_3131_);
v___x_3125_ = v___x_3123_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_dec(v___x_3123_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v___x_3105_);
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3105_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec(v___x_3105_);
v_a_3132_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3123_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3123_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v___x_3094_);
v_a_3142_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3101_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3101_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec_ref(v_preDefs_3081_);
v_a_3150_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3089_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3089_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_);
lean_dec(v_a_3162_);
lean_dec_ref(v_a_3161_);
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_upperBound_3165_, lean_object* v_val_3166_, lean_object* v_next_3167_, lean_object* v_params_3168_, lean_object* v___x_3169_, lean_object* v_val_3170_, lean_object* v_next_3171_, uint8_t v___x_3172_, lean_object* v_inst_3173_, lean_object* v_R_3174_, lean_object* v_a_3175_, uint8_t v_b_3176_, lean_object* v_c_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_3165_, v_val_3166_, v_next_3167_, v_params_3168_, v___x_3169_, v_val_3170_, v_next_3171_, v___x_3172_, v_a_3175_, v_b_3176_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3184_ = _args[0];
lean_object* v_val_3185_ = _args[1];
lean_object* v_next_3186_ = _args[2];
lean_object* v_params_3187_ = _args[3];
lean_object* v___x_3188_ = _args[4];
lean_object* v_val_3189_ = _args[5];
lean_object* v_next_3190_ = _args[6];
lean_object* v___x_3191_ = _args[7];
lean_object* v_inst_3192_ = _args[8];
lean_object* v_R_3193_ = _args[9];
lean_object* v_a_3194_ = _args[10];
lean_object* v_b_3195_ = _args[11];
lean_object* v_c_3196_ = _args[12];
lean_object* v___y_3197_ = _args[13];
lean_object* v___y_3198_ = _args[14];
lean_object* v___y_3199_ = _args[15];
lean_object* v___y_3200_ = _args[16];
lean_object* v___y_3201_ = _args[17];
_start:
{
uint8_t v___x_44851__boxed_3202_; uint8_t v_b_boxed_3203_; lean_object* v_res_3204_; 
v___x_44851__boxed_3202_ = lean_unbox(v___x_3191_);
v_b_boxed_3203_ = lean_unbox(v_b_3195_);
v_res_3204_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_upperBound_3184_, v_val_3185_, v_next_3186_, v_params_3187_, v___x_3188_, v_val_3189_, v_next_3190_, v___x_44851__boxed_3202_, v_inst_3192_, v_R_3193_, v_a_3194_, v_b_boxed_3203_, v_c_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v_val_3189_);
lean_dec_ref(v_params_3187_);
lean_dec(v_next_3186_);
lean_dec(v_val_3185_);
lean_dec(v_upperBound_3184_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3205_, lean_object* v_val_3206_, lean_object* v_upperBound_3207_, lean_object* v_args_3208_, lean_object* v_e_3209_, lean_object* v_next_3210_, lean_object* v_params_3211_, lean_object* v___x_3212_, uint8_t v___x_3213_, lean_object* v_inst_3214_, lean_object* v_R_3215_, lean_object* v_a_3216_, lean_object* v_b_3217_, lean_object* v_c_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3205_, v_val_3206_, v_upperBound_3207_, v_args_3208_, v_e_3209_, v_next_3210_, v_params_3211_, v___x_3212_, v___x_3213_, v_a_3216_, v_b_3217_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3225_ = _args[0];
lean_object* v_val_3226_ = _args[1];
lean_object* v_upperBound_3227_ = _args[2];
lean_object* v_args_3228_ = _args[3];
lean_object* v_e_3229_ = _args[4];
lean_object* v_next_3230_ = _args[5];
lean_object* v_params_3231_ = _args[6];
lean_object* v___x_3232_ = _args[7];
lean_object* v___x_3233_ = _args[8];
lean_object* v_inst_3234_ = _args[9];
lean_object* v_R_3235_ = _args[10];
lean_object* v_a_3236_ = _args[11];
lean_object* v_b_3237_ = _args[12];
lean_object* v_c_3238_ = _args[13];
lean_object* v___y_3239_ = _args[14];
lean_object* v___y_3240_ = _args[15];
lean_object* v___y_3241_ = _args[16];
lean_object* v___y_3242_ = _args[17];
lean_object* v___y_3243_ = _args[18];
_start:
{
uint8_t v___x_44886__boxed_3244_; lean_object* v_res_3245_; 
v___x_44886__boxed_3244_ = lean_unbox(v___x_3233_);
v_res_3245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3225_, v_val_3226_, v_upperBound_3227_, v_args_3228_, v_e_3229_, v_next_3230_, v_params_3231_, v___x_3232_, v___x_44886__boxed_3244_, v_inst_3234_, v_R_3235_, v_a_3236_, v_b_3237_, v_c_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___x_3232_);
lean_dec_ref(v_params_3231_);
lean_dec(v_next_3230_);
lean_dec_ref(v_args_3228_);
lean_dec(v_upperBound_3227_);
lean_dec(v_val_3225_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v_preDefs_3246_, lean_object* v___x_3247_, lean_object* v_val_3248_, lean_object* v_upperBound_3249_, lean_object* v_inst_3250_, lean_object* v_R_3251_, lean_object* v_a_3252_, lean_object* v_b_3253_, lean_object* v_c_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3246_, v___x_3247_, v_val_3248_, v_upperBound_3249_, v_a_3252_, v_b_3253_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v_preDefs_3261_, lean_object* v___x_3262_, lean_object* v_val_3263_, lean_object* v_upperBound_3264_, lean_object* v_inst_3265_, lean_object* v_R_3266_, lean_object* v_a_3267_, lean_object* v_b_3268_, lean_object* v_c_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v_preDefs_3261_, v___x_3262_, v_val_3263_, v_upperBound_3264_, v_inst_3265_, v_R_3266_, v_a_3267_, v_b_3268_, v_c_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v_upperBound_3264_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3276_, lean_object* v___x_3277_, lean_object* v_pre_3278_, lean_object* v_post_3279_, uint8_t v_usedLetOnly_3280_, uint8_t v_skipConstInApp_3281_, uint8_t v_skipInstances_3282_, lean_object* v___x_3283_, lean_object* v_inst_3284_, lean_object* v_R_3285_, lean_object* v_a_3286_, lean_object* v_b_3287_, lean_object* v_c_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3276_, v___x_3277_, v_pre_3278_, v_post_3279_, v_usedLetOnly_3280_, v_skipConstInApp_3281_, v_skipInstances_3282_, v_a_3286_, v_b_3287_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3296_ = _args[0];
lean_object* v___x_3297_ = _args[1];
lean_object* v_pre_3298_ = _args[2];
lean_object* v_post_3299_ = _args[3];
lean_object* v_usedLetOnly_3300_ = _args[4];
lean_object* v_skipConstInApp_3301_ = _args[5];
lean_object* v_skipInstances_3302_ = _args[6];
lean_object* v___x_3303_ = _args[7];
lean_object* v_inst_3304_ = _args[8];
lean_object* v_R_3305_ = _args[9];
lean_object* v_a_3306_ = _args[10];
lean_object* v_b_3307_ = _args[11];
lean_object* v_c_3308_ = _args[12];
lean_object* v___y_3309_ = _args[13];
lean_object* v___y_3310_ = _args[14];
lean_object* v___y_3311_ = _args[15];
lean_object* v___y_3312_ = _args[16];
lean_object* v___y_3313_ = _args[17];
lean_object* v___y_3314_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3315_; uint8_t v_skipConstInApp_boxed_3316_; uint8_t v_skipInstances_boxed_3317_; lean_object* v_res_3318_; 
v_usedLetOnly_boxed_3315_ = lean_unbox(v_usedLetOnly_3300_);
v_skipConstInApp_boxed_3316_ = lean_unbox(v_skipConstInApp_3301_);
v_skipInstances_boxed_3317_ = lean_unbox(v_skipInstances_3302_);
v_res_3318_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3296_, v___x_3297_, v_pre_3298_, v_post_3299_, v_usedLetOnly_boxed_3315_, v_skipConstInApp_boxed_3316_, v_skipInstances_boxed_3317_, v___x_3303_, v_inst_3304_, v_R_3305_, v_a_3306_, v_b_3307_, v_c_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec(v___x_3303_);
lean_dec_ref(v___x_3297_);
lean_dec(v_upperBound_3296_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3319_, lean_object* v_m_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3320_, v_a_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3323_, lean_object* v_m_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3323_, v_m_3324_, v_a_3325_);
lean_dec_ref(v_a_3325_);
lean_dec_ref(v_m_3324_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3327_, lean_object* v_name_3328_, uint8_t v_bi_3329_, lean_object* v_type_3330_, lean_object* v_k_3331_, uint8_t v_kind_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3328_, v_bi_3329_, v_type_3330_, v_k_3331_, v_kind_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3340_, lean_object* v_name_3341_, lean_object* v_bi_3342_, lean_object* v_type_3343_, lean_object* v_k_3344_, lean_object* v_kind_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
uint8_t v_bi_boxed_3352_; uint8_t v_kind_boxed_3353_; lean_object* v_res_3354_; 
v_bi_boxed_3352_ = lean_unbox(v_bi_3342_);
v_kind_boxed_3353_ = lean_unbox(v_kind_3345_);
v_res_3354_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3340_, v_name_3341_, v_bi_boxed_3352_, v_type_3343_, v_k_3344_, v_kind_boxed_3353_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3355_, lean_object* v_name_3356_, lean_object* v_type_3357_, lean_object* v_val_3358_, lean_object* v_k_3359_, uint8_t v_nondep_3360_, uint8_t v_kind_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3356_, v_type_3357_, v_val_3358_, v_k_3359_, v_nondep_3360_, v_kind_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3369_, lean_object* v_name_3370_, lean_object* v_type_3371_, lean_object* v_val_3372_, lean_object* v_k_3373_, lean_object* v_nondep_3374_, lean_object* v_kind_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
uint8_t v_nondep_boxed_3382_; uint8_t v_kind_boxed_3383_; lean_object* v_res_3384_; 
v_nondep_boxed_3382_ = lean_unbox(v_nondep_3374_);
v_kind_boxed_3383_ = lean_unbox(v_kind_3375_);
v_res_3384_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3369_, v_name_3370_, v_type_3371_, v_val_3372_, v_k_3373_, v_nondep_boxed_3382_, v_kind_boxed_3383_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3385_, lean_object* v_ref_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3386_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3393_, lean_object* v_ref_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3393_, v_ref_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3401_, lean_object* v_x_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3410_, lean_object* v_x_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3410_, v_x_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3419_, lean_object* v_m_3420_, lean_object* v_query_3421_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3420_, v_query_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___boxed(lean_object* v_00_u03b2_3423_, lean_object* v_m_3424_, lean_object* v_query_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(v_00_u03b2_3423_, v_m_3424_, v_query_3425_);
lean_dec_ref(v_query_3425_);
lean_dec_ref(v_m_3424_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20(lean_object* v_00_u03b2_3427_, lean_object* v_m_3428_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20___redArg(v_m_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20___boxed(lean_object* v_00_u03b2_3430_, lean_object* v_m_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20(v_00_u03b2_3430_, v_m_3431_);
lean_dec_ref(v_m_3431_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3433_, lean_object* v_m_3434_, lean_object* v_query_3435_){
_start:
{
lean_object* v___x_3436_; 
v___x_3436_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_m_3434_, v_query_3435_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3437_, lean_object* v_m_3438_, lean_object* v_query_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3437_, v_m_3438_, v_query_3439_);
lean_dec_ref(v_query_3439_);
lean_dec_ref(v_m_3438_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3441_, lean_object* v_m_3442_, lean_object* v_query_3443_, lean_object* v_x_3444_, lean_object* v_x_3445_, lean_object* v_x_3446_, lean_object* v_x_3447_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_m_3442_, v_query_3443_, v_x_3444_, v_x_3445_, v_x_3446_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3449_, lean_object* v_m_3450_, lean_object* v_query_3451_, lean_object* v_x_3452_, lean_object* v_x_3453_, lean_object* v_x_3454_, lean_object* v_x_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3449_, v_m_3450_, v_query_3451_, v_x_3452_, v_x_3453_, v_x_3454_, v_x_3455_);
lean_dec_ref(v_query_3451_);
lean_dec_ref(v_m_3450_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27(lean_object* v_00_u03b2_3457_, lean_object* v_init_3458_, lean_object* v_b_3459_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27___redArg(v_init_3458_, v_b_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27___boxed(lean_object* v_00_u03b2_3461_, lean_object* v_init_3462_, lean_object* v_b_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27(v_00_u03b2_3461_, v_init_3462_, v_b_3463_);
lean_dec_ref(v_b_3463_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27_spec__28(lean_object* v_00_u03b2_3465_, lean_object* v_b_3466_, lean_object* v_acc_3467_, lean_object* v_i_3468_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27_spec__28___redArg(v_b_3466_, v_acc_3467_, v_i_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27_spec__28___boxed(lean_object* v_00_u03b2_3470_, lean_object* v_b_3471_, lean_object* v_acc_3472_, lean_object* v_i_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__20_spec__27_spec__28(v_00_u03b2_3470_, v_b_3471_, v_acc_3472_, v_i_3473_);
lean_dec_ref(v_b_3471_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3488_, lean_object* v_x_3489_){
_start:
{
if (lean_obj_tag(v_x_3488_) == 0)
{
lean_object* v___x_3490_; 
v___x_3490_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3490_;
}
else
{
lean_object* v_val_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3502_; 
v_val_3491_ = lean_ctor_get(v_x_3488_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_x_3488_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3493_ = v_x_3488_;
v_isShared_3494_ = v_isSharedCheck_3502_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_val_3491_);
lean_dec(v_x_3488_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3502_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3495_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3496_ = l_Nat_reprFast(v_val_3491_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set_tag(v___x_3493_, 3);
lean_ctor_set(v___x_3493_, 0, v___x_3496_);
v___x_3498_ = v___x_3493_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3495_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = l_Repr_addAppParen(v___x_3499_, v_x_3489_);
return v___x_3500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3503_, lean_object* v_x_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3503_, v_x_3504_);
lean_dec(v_x_3504_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3506_, lean_object* v_x_3507_, lean_object* v_x_3508_){
_start:
{
if (lean_obj_tag(v_x_3508_) == 0)
{
lean_dec(v_x_3506_);
return v_x_3507_;
}
else
{
lean_object* v_head_3509_; lean_object* v_tail_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3521_; 
v_head_3509_ = lean_ctor_get(v_x_3508_, 0);
v_tail_3510_ = lean_ctor_get(v_x_3508_, 1);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_x_3508_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3512_ = v_x_3508_;
v_isShared_3513_ = v_isSharedCheck_3521_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_tail_3510_);
lean_inc(v_head_3509_);
lean_dec(v_x_3508_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3521_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
lean_inc(v_x_3506_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set_tag(v___x_3512_, 5);
lean_ctor_set(v___x_3512_, 1, v_x_3506_);
lean_ctor_set(v___x_3512_, 0, v_x_3507_);
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_x_3507_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_x_3506_);
v___x_3515_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = lean_unsigned_to_nat(0u);
v___x_3517_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3509_, v___x_3516_);
v___x_3518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3515_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
v_x_3507_ = v___x_3518_;
v_x_3508_ = v_tail_3510_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3522_, lean_object* v_x_3523_, lean_object* v_x_3524_){
_start:
{
if (lean_obj_tag(v_x_3524_) == 0)
{
lean_dec(v_x_3522_);
return v_x_3523_;
}
else
{
lean_object* v_head_3525_; lean_object* v_tail_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3537_; 
v_head_3525_ = lean_ctor_get(v_x_3524_, 0);
v_tail_3526_ = lean_ctor_get(v_x_3524_, 1);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_x_3524_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3528_ = v_x_3524_;
v_isShared_3529_ = v_isSharedCheck_3537_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_tail_3526_);
lean_inc(v_head_3525_);
lean_dec(v_x_3524_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3537_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
lean_inc(v_x_3522_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set_tag(v___x_3528_, 5);
lean_ctor_set(v___x_3528_, 1, v_x_3522_);
lean_ctor_set(v___x_3528_, 0, v_x_3523_);
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_x_3523_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_x_3522_);
v___x_3531_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3532_ = lean_unsigned_to_nat(0u);
v___x_3533_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3525_, v___x_3532_);
v___x_3534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3531_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3522_, v___x_3534_, v_tail_3526_);
return v___x_3535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = lean_unsigned_to_nat(0u);
v___x_3540_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3538_, v___x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3541_, lean_object* v_x_3542_){
_start:
{
if (lean_obj_tag(v_x_3541_) == 0)
{
lean_object* v___x_3543_; 
lean_dec(v_x_3542_);
v___x_3543_ = lean_box(0);
return v___x_3543_;
}
else
{
lean_object* v_tail_3544_; 
v_tail_3544_ = lean_ctor_get(v_x_3541_, 1);
if (lean_obj_tag(v_tail_3544_) == 0)
{
lean_object* v_head_3545_; lean_object* v___x_3546_; 
lean_dec(v_x_3542_);
v_head_3545_ = lean_ctor_get(v_x_3541_, 0);
lean_inc(v_head_3545_);
lean_dec_ref_known(v_x_3541_, 2);
v___x_3546_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3545_);
return v___x_3546_;
}
else
{
lean_object* v_head_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
lean_inc(v_tail_3544_);
v_head_3547_ = lean_ctor_get(v_x_3541_, 0);
lean_inc(v_head_3547_);
lean_dec_ref_known(v_x_3541_, 2);
v___x_3548_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3547_);
v___x_3549_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3542_, v___x_3548_, v_tail_3544_);
return v___x_3549_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3558_ = lean_string_length(v___x_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3560_ = lean_nat_to_int(v___x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3566_){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; 
v___x_3567_ = lean_array_get_size(v_xs_3566_);
v___x_3568_ = lean_unsigned_to_nat(0u);
v___x_3569_ = lean_nat_dec_eq(v___x_3567_, v___x_3568_);
if (v___x_3569_ == 0)
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3570_ = lean_array_to_list(v_xs_3566_);
v___x_3571_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3572_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3570_, v___x_3571_);
v___x_3573_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3574_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
lean_ctor_set(v___x_3575_, 1, v___x_3572_);
v___x_3576_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3575_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
v___x_3578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3573_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = l_Std_Format_fill(v___x_3578_);
return v___x_3579_;
}
else
{
lean_object* v___x_3580_; 
lean_dec_ref(v_xs_3566_);
v___x_3580_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3580_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3581_, lean_object* v_x_3582_, lean_object* v_x_3583_){
_start:
{
if (lean_obj_tag(v_x_3583_) == 0)
{
lean_dec(v_x_3581_);
return v_x_3582_;
}
else
{
lean_object* v_head_3584_; lean_object* v_tail_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3595_; 
v_head_3584_ = lean_ctor_get(v_x_3583_, 0);
v_tail_3585_ = lean_ctor_get(v_x_3583_, 1);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_x_3583_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3587_ = v_x_3583_;
v_isShared_3588_ = v_isSharedCheck_3595_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_tail_3585_);
lean_inc(v_head_3584_);
lean_dec(v_x_3583_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3595_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
lean_inc(v_x_3581_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set_tag(v___x_3587_, 5);
lean_ctor_set(v___x_3587_, 1, v_x_3581_);
lean_ctor_set(v___x_3587_, 0, v_x_3582_);
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_x_3582_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_x_3581_);
v___x_3590_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3584_);
v___x_3592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3590_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
v_x_3582_ = v___x_3592_;
v_x_3583_ = v_tail_3585_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
if (lean_obj_tag(v_x_3596_) == 0)
{
lean_object* v___x_3598_; 
lean_dec(v_x_3597_);
v___x_3598_ = lean_box(0);
return v___x_3598_;
}
else
{
lean_object* v_tail_3599_; 
v_tail_3599_ = lean_ctor_get(v_x_3596_, 1);
if (lean_obj_tag(v_tail_3599_) == 0)
{
lean_object* v_head_3600_; lean_object* v___x_3601_; 
lean_dec(v_x_3597_);
v_head_3600_ = lean_ctor_get(v_x_3596_, 0);
lean_inc(v_head_3600_);
lean_dec_ref_known(v_x_3596_, 2);
v___x_3601_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3600_);
return v___x_3601_;
}
else
{
lean_object* v_head_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
lean_inc(v_tail_3599_);
v_head_3602_ = lean_ctor_get(v_x_3596_, 0);
lean_inc(v_head_3602_);
lean_dec_ref_known(v_x_3596_, 2);
v___x_3603_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3602_);
v___x_3604_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3597_, v___x_3603_, v_tail_3599_);
return v___x_3604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3605_){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
v___x_3606_ = lean_array_get_size(v_xs_3605_);
v___x_3607_ = lean_unsigned_to_nat(0u);
v___x_3608_ = lean_nat_dec_eq(v___x_3606_, v___x_3607_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3609_ = lean_array_to_list(v_xs_3605_);
v___x_3610_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3611_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3609_, v___x_3610_);
v___x_3612_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3613_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
lean_ctor_set(v___x_3614_, 1, v___x_3611_);
v___x_3615_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3614_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
v___x_3617_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3612_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = l_Std_Format_fill(v___x_3617_);
return v___x_3618_;
}
else
{
lean_object* v___x_3619_; 
lean_dec_ref(v_xs_3605_);
v___x_3619_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3619_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3620_, lean_object* v_x_3621_, lean_object* v_x_3622_){
_start:
{
if (lean_obj_tag(v_x_3622_) == 0)
{
lean_dec(v_x_3620_);
return v_x_3621_;
}
else
{
lean_object* v_head_3623_; lean_object* v_tail_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3635_; 
v_head_3623_ = lean_ctor_get(v_x_3622_, 0);
v_tail_3624_ = lean_ctor_get(v_x_3622_, 1);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_x_3622_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3626_ = v_x_3622_;
v_isShared_3627_ = v_isSharedCheck_3635_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_tail_3624_);
lean_inc(v_head_3623_);
lean_dec(v_x_3622_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3635_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
lean_inc(v_x_3620_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set_tag(v___x_3626_, 5);
lean_ctor_set(v___x_3626_, 1, v_x_3620_);
lean_ctor_set(v___x_3626_, 0, v_x_3621_);
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_x_3621_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_x_3620_);
v___x_3629_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3630_ = l_Nat_reprFast(v_head_3623_);
v___x_3631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
v___x_3632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3629_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v_x_3621_ = v___x_3632_;
v_x_3622_ = v_tail_3624_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3636_, lean_object* v_x_3637_, lean_object* v_x_3638_){
_start:
{
if (lean_obj_tag(v_x_3638_) == 0)
{
lean_dec(v_x_3636_);
return v_x_3637_;
}
else
{
lean_object* v_head_3639_; lean_object* v_tail_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3651_; 
v_head_3639_ = lean_ctor_get(v_x_3638_, 0);
v_tail_3640_ = lean_ctor_get(v_x_3638_, 1);
v_isSharedCheck_3651_ = !lean_is_exclusive(v_x_3638_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3642_ = v_x_3638_;
v_isShared_3643_ = v_isSharedCheck_3651_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_tail_3640_);
lean_inc(v_head_3639_);
lean_dec(v_x_3638_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3651_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
lean_inc(v_x_3636_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set_tag(v___x_3642_, 5);
lean_ctor_set(v___x_3642_, 1, v_x_3636_);
lean_ctor_set(v___x_3642_, 0, v_x_3637_);
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_x_3637_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_x_3636_);
v___x_3645_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3646_ = l_Nat_reprFast(v_head_3639_);
v___x_3647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
v___x_3648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3645_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3636_, v___x_3648_, v_tail_3640_);
return v___x_3649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = l_Nat_reprFast(v___y_3652_);
v___x_3654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3655_, lean_object* v_x_3656_){
_start:
{
if (lean_obj_tag(v_x_3655_) == 0)
{
lean_object* v___x_3657_; 
lean_dec(v_x_3656_);
v___x_3657_ = lean_box(0);
return v___x_3657_;
}
else
{
lean_object* v_tail_3658_; 
v_tail_3658_ = lean_ctor_get(v_x_3655_, 1);
if (lean_obj_tag(v_tail_3658_) == 0)
{
lean_object* v_head_3659_; lean_object* v___x_3660_; 
lean_dec(v_x_3656_);
v_head_3659_ = lean_ctor_get(v_x_3655_, 0);
lean_inc(v_head_3659_);
lean_dec_ref_known(v_x_3655_, 2);
v___x_3660_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3659_);
return v___x_3660_;
}
else
{
lean_object* v_head_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
lean_inc(v_tail_3658_);
v_head_3661_ = lean_ctor_get(v_x_3655_, 0);
lean_inc(v_head_3661_);
lean_dec_ref_known(v_x_3655_, 2);
v___x_3662_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3661_);
v___x_3663_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3656_, v___x_3662_, v_tail_3658_);
return v___x_3663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3664_){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v___x_3665_ = lean_array_get_size(v_xs_3664_);
v___x_3666_ = lean_unsigned_to_nat(0u);
v___x_3667_ = lean_nat_dec_eq(v___x_3665_, v___x_3666_);
if (v___x_3667_ == 0)
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3668_ = lean_array_to_list(v_xs_3664_);
v___x_3669_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3670_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3668_, v___x_3669_);
v___x_3671_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3672_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
lean_ctor_set(v___x_3673_, 1, v___x_3670_);
v___x_3674_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3673_);
lean_ctor_set(v___x_3675_, 1, v___x_3674_);
v___x_3676_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3671_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
v___x_3677_ = l_Std_Format_fill(v___x_3676_);
return v___x_3677_;
}
else
{
lean_object* v___x_3678_; 
lean_dec_ref(v_xs_3664_);
v___x_3678_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3678_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3679_, lean_object* v_x_3680_, lean_object* v_x_3681_){
_start:
{
if (lean_obj_tag(v_x_3681_) == 0)
{
lean_dec(v_x_3679_);
return v_x_3680_;
}
else
{
lean_object* v_head_3682_; lean_object* v_tail_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3693_; 
v_head_3682_ = lean_ctor_get(v_x_3681_, 0);
v_tail_3683_ = lean_ctor_get(v_x_3681_, 1);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_x_3681_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3685_ = v_x_3681_;
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_tail_3683_);
lean_inc(v_head_3682_);
lean_dec(v_x_3681_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
lean_inc(v_x_3679_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set_tag(v___x_3685_, 5);
lean_ctor_set(v___x_3685_, 1, v_x_3679_);
lean_ctor_set(v___x_3685_, 0, v_x_3680_);
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_x_3680_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_x_3679_);
v___x_3688_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3682_);
v___x_3690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v_x_3680_ = v___x_3690_;
v_x_3681_ = v_tail_3683_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3694_, lean_object* v_x_3695_){
_start:
{
if (lean_obj_tag(v_x_3694_) == 0)
{
lean_object* v___x_3696_; 
lean_dec(v_x_3695_);
v___x_3696_ = lean_box(0);
return v___x_3696_;
}
else
{
lean_object* v_tail_3697_; 
v_tail_3697_ = lean_ctor_get(v_x_3694_, 1);
if (lean_obj_tag(v_tail_3697_) == 0)
{
lean_object* v_head_3698_; lean_object* v___x_3699_; 
lean_dec(v_x_3695_);
v_head_3698_ = lean_ctor_get(v_x_3694_, 0);
lean_inc(v_head_3698_);
lean_dec_ref_known(v_x_3694_, 2);
v___x_3699_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3698_);
return v___x_3699_;
}
else
{
lean_object* v_head_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_inc(v_tail_3697_);
v_head_3700_ = lean_ctor_get(v_x_3694_, 0);
lean_inc(v_head_3700_);
lean_dec_ref_known(v_x_3694_, 2);
v___x_3701_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3700_);
v___x_3702_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3695_, v___x_3701_, v_tail_3697_);
return v___x_3702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3703_){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v___x_3704_ = lean_array_get_size(v_xs_3703_);
v___x_3705_ = lean_unsigned_to_nat(0u);
v___x_3706_ = lean_nat_dec_eq(v___x_3704_, v___x_3705_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3707_ = lean_array_to_list(v_xs_3703_);
v___x_3708_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3709_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3707_, v___x_3708_);
v___x_3710_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3711_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
lean_ctor_set(v___x_3712_, 1, v___x_3709_);
v___x_3713_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3710_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = l_Std_Format_fill(v___x_3715_);
return v___x_3716_;
}
else
{
lean_object* v___x_3717_; 
lean_dec_ref(v_xs_3703_);
v___x_3717_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3717_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3718_, lean_object* v_x_3719_, lean_object* v_x_3720_){
_start:
{
if (lean_obj_tag(v_x_3720_) == 0)
{
lean_dec(v_x_3718_);
return v_x_3719_;
}
else
{
lean_object* v_head_3721_; lean_object* v_tail_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3732_; 
v_head_3721_ = lean_ctor_get(v_x_3720_, 0);
v_tail_3722_ = lean_ctor_get(v_x_3720_, 1);
v_isSharedCheck_3732_ = !lean_is_exclusive(v_x_3720_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3724_ = v_x_3720_;
v_isShared_3725_ = v_isSharedCheck_3732_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_tail_3722_);
lean_inc(v_head_3721_);
lean_dec(v_x_3720_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3732_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
lean_inc(v_x_3718_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set_tag(v___x_3724_, 5);
lean_ctor_set(v___x_3724_, 1, v_x_3718_);
lean_ctor_set(v___x_3724_, 0, v_x_3719_);
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_x_3719_);
lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_x_3718_);
v___x_3727_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3721_);
v___x_3729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v_x_3719_ = v___x_3729_;
v_x_3720_ = v_tail_3722_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3733_, lean_object* v_x_3734_){
_start:
{
if (lean_obj_tag(v_x_3733_) == 0)
{
lean_object* v___x_3735_; 
lean_dec(v_x_3734_);
v___x_3735_ = lean_box(0);
return v___x_3735_;
}
else
{
lean_object* v_tail_3736_; 
v_tail_3736_ = lean_ctor_get(v_x_3733_, 1);
if (lean_obj_tag(v_tail_3736_) == 0)
{
lean_object* v_head_3737_; lean_object* v___x_3738_; 
lean_dec(v_x_3734_);
v_head_3737_ = lean_ctor_get(v_x_3733_, 0);
lean_inc(v_head_3737_);
lean_dec_ref_known(v_x_3733_, 2);
v___x_3738_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3737_);
return v___x_3738_;
}
else
{
lean_object* v_head_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_inc(v_tail_3736_);
v_head_3739_ = lean_ctor_get(v_x_3733_, 0);
lean_inc(v_head_3739_);
lean_dec_ref_known(v_x_3733_, 2);
v___x_3740_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3739_);
v___x_3741_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3734_, v___x_3740_, v_tail_3736_);
return v___x_3741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3742_){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; uint8_t v___x_3745_; 
v___x_3743_ = lean_array_get_size(v_xs_3742_);
v___x_3744_ = lean_unsigned_to_nat(0u);
v___x_3745_ = lean_nat_dec_eq(v___x_3743_, v___x_3744_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3746_ = lean_array_to_list(v_xs_3742_);
v___x_3747_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3748_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3746_, v___x_3747_);
v___x_3749_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3750_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
lean_ctor_set(v___x_3751_, 1, v___x_3748_);
v___x_3752_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3751_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3749_);
lean_ctor_set(v___x_3754_, 1, v___x_3753_);
v___x_3755_ = l_Std_Format_fill(v___x_3754_);
return v___x_3755_;
}
else
{
lean_object* v___x_3756_; 
lean_dec_ref(v_xs_3742_);
v___x_3756_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3756_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = lean_unsigned_to_nat(12u);
v___x_3771_ = lean_nat_to_int(v___x_3770_);
return v___x_3771_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = lean_unsigned_to_nat(9u);
v___x_3776_ = lean_nat_to_int(v___x_3775_);
return v___x_3776_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = lean_unsigned_to_nat(11u);
v___x_3781_ = lean_nat_to_int(v___x_3780_);
return v___x_3781_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3783_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3784_ = lean_string_length(v___x_3783_);
return v___x_3784_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3786_ = lean_nat_to_int(v___x_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3791_){
_start:
{
lean_object* v_numFixed_3792_; lean_object* v_perms_3793_; lean_object* v_revDeps_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v_numFixed_3792_ = lean_ctor_get(v_x_3791_, 0);
lean_inc(v_numFixed_3792_);
v_perms_3793_ = lean_ctor_get(v_x_3791_, 1);
lean_inc_ref(v_perms_3793_);
v_revDeps_3794_ = lean_ctor_get(v_x_3791_, 2);
lean_inc_ref(v_revDeps_3794_);
lean_dec_ref(v_x_3791_);
v___x_3795_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3796_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3797_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3798_ = l_Nat_reprFast(v_numFixed_3792_);
v___x_3799_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
v___x_3800_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3797_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = 0;
v___x_3802_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3802_, 0, v___x_3800_);
lean_ctor_set_uint8(v___x_3802_, sizeof(void*)*1, v___x_3801_);
v___x_3803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3796_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3803_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
v___x_3806_ = lean_box(1);
v___x_3807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3805_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
lean_ctor_set(v___x_3810_, 1, v___x_3795_);
v___x_3811_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3812_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3793_);
v___x_3813_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3811_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set_uint8(v___x_3814_, sizeof(void*)*1, v___x_3801_);
v___x_3815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3810_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
lean_ctor_set(v___x_3816_, 1, v___x_3804_);
v___x_3817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
lean_ctor_set(v___x_3817_, 1, v___x_3806_);
v___x_3818_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3817_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
v___x_3820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
lean_ctor_set(v___x_3820_, 1, v___x_3795_);
v___x_3821_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3822_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3794_);
v___x_3823_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3821_);
lean_ctor_set(v___x_3823_, 1, v___x_3822_);
v___x_3824_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
lean_ctor_set_uint8(v___x_3824_, sizeof(void*)*1, v___x_3801_);
v___x_3825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3820_);
lean_ctor_set(v___x_3825_, 1, v___x_3824_);
v___x_3826_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3827_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3827_);
lean_ctor_set(v___x_3828_, 1, v___x_3825_);
v___x_3829_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3828_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
v___x_3831_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3826_);
lean_ctor_set(v___x_3831_, 1, v___x_3830_);
v___x_3832_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
lean_ctor_set_uint8(v___x_3832_, sizeof(void*)*1, v___x_3801_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3833_, lean_object* v_prec_3834_){
_start:
{
lean_object* v___x_3835_; 
v___x_3835_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3833_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3836_, lean_object* v_prec_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3836_, v_prec_3837_);
lean_dec(v_prec_3837_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v___f_3847_; lean_object* v___x_5797__overap_3848_; lean_object* v___x_3849_; 
v___f_3847_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5797__overap_3848_ = lean_panic_fn_borrowed(v___f_3847_, v_msg_3841_);
lean_inc(v___y_3845_);
lean_inc_ref(v___y_3844_);
lean_inc(v___y_3843_);
lean_inc_ref(v___y_3842_);
v___x_3849_ = lean_apply_5(v___x_5797__overap_3848_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, lean_box(0));
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v___f_3863_; lean_object* v___x_5807__overap_3864_; lean_object* v___x_3865_; 
v___f_3863_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5807__overap_3864_ = lean_panic_fn_borrowed(v___f_3863_, v_msg_3857_);
lean_inc(v___y_3861_);
lean_inc_ref(v___y_3860_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
v___x_3865_ = lean_apply_5(v___x_5807__overap_3864_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, lean_box(0));
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___f_3879_; lean_object* v___x_5817__overap_3880_; lean_object* v___x_3881_; 
v___f_3879_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5817__overap_3880_ = lean_panic_fn_borrowed(v___f_3879_, v_msg_3873_);
lean_inc(v___y_3877_);
lean_inc_ref(v___y_3876_);
lean_inc(v___y_3875_);
lean_inc_ref(v___y_3874_);
v___x_3881_ = lean_apply_5(v___x_5817__overap_3880_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, lean_box(0));
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
return v_res_3888_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3891_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1));
v___x_3892_ = lean_unsigned_to_nat(8u);
v___x_3893_ = lean_unsigned_to_nat(281u);
v___x_3894_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3895_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3896_ = l_mkPanicMessageWithDecl(v___x_3895_, v___x_3894_, v___x_3893_, v___x_3892_, v___x_3891_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3897_, lean_object* v_a_3898_, lean_object* v_b_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v_a_3906_; uint8_t v___x_3910_; 
v___x_3910_ = lean_nat_dec_lt(v_a_3898_, v_upperBound_3897_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; 
lean_dec(v_a_3898_);
v___x_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3911_, 0, v_b_3899_);
return v___x_3911_;
}
else
{
lean_object* v_snd_3912_; lean_object* v_snd_3913_; lean_object* v_snd_3914_; lean_object* v_fst_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_4039_; 
v_snd_3912_ = lean_ctor_get(v_b_3899_, 1);
lean_inc(v_snd_3912_);
v_snd_3913_ = lean_ctor_get(v_snd_3912_, 1);
lean_inc(v_snd_3913_);
v_snd_3914_ = lean_ctor_get(v_snd_3913_, 1);
lean_inc(v_snd_3914_);
v_fst_3915_ = lean_ctor_get(v_b_3899_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v_b_3899_);
if (v_isSharedCheck_4039_ == 0)
{
lean_object* v_unused_4040_; 
v_unused_4040_ = lean_ctor_get(v_b_3899_, 1);
lean_dec(v_unused_4040_);
v___x_3917_ = v_b_3899_;
v_isShared_3918_ = v_isSharedCheck_4039_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_fst_3915_);
lean_dec(v_b_3899_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_4039_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v_fst_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_4037_; 
v_fst_3919_ = lean_ctor_get(v_snd_3912_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v_snd_3912_);
if (v_isSharedCheck_4037_ == 0)
{
lean_object* v_unused_4038_; 
v_unused_4038_ = lean_ctor_get(v_snd_3912_, 1);
lean_dec(v_unused_4038_);
v___x_3921_ = v_snd_3912_;
v_isShared_3922_ = v_isSharedCheck_4037_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_fst_3919_);
lean_dec(v_snd_3912_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_4037_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v_fst_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_4035_; 
v_fst_3923_ = lean_ctor_get(v_snd_3913_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v_snd_3913_);
if (v_isSharedCheck_4035_ == 0)
{
lean_object* v_unused_4036_; 
v_unused_4036_ = lean_ctor_get(v_snd_3913_, 1);
lean_dec(v_unused_4036_);
v___x_3925_ = v_snd_3913_;
v_isShared_3926_ = v_isSharedCheck_4035_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_fst_3923_);
lean_dec(v_snd_3913_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_4035_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v_array_3927_; lean_object* v_start_3928_; lean_object* v_stop_3929_; uint8_t v___x_3930_; 
v_array_3927_ = lean_ctor_get(v_snd_3914_, 0);
v_start_3928_ = lean_ctor_get(v_snd_3914_, 1);
v_stop_3929_ = lean_ctor_get(v_snd_3914_, 2);
v___x_3930_ = lean_nat_dec_lt(v_start_3928_, v_stop_3929_);
if (v___x_3930_ == 0)
{
lean_object* v___x_3932_; 
lean_dec(v_a_3898_);
if (v_isShared_3926_ == 0)
{
v___x_3932_ = v___x_3925_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_fst_3923_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_snd_3914_);
v___x_3932_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3934_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 1, v___x_3932_);
v___x_3934_ = v___x_3921_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_fst_3919_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3936_; 
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 1, v___x_3934_);
v___x_3936_ = v___x_3917_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_fst_3915_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v___x_3934_);
v___x_3936_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
lean_object* v___x_3937_; 
v___x_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
return v___x_3937_;
}
}
}
}
else
{
lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_4031_; 
lean_inc(v_stop_3929_);
lean_inc(v_start_3928_);
lean_inc_ref(v_array_3927_);
v_isSharedCheck_4031_ = !lean_is_exclusive(v_snd_3914_);
if (v_isSharedCheck_4031_ == 0)
{
lean_object* v_unused_4032_; lean_object* v_unused_4033_; lean_object* v_unused_4034_; 
v_unused_4032_ = lean_ctor_get(v_snd_3914_, 2);
lean_dec(v_unused_4032_);
v_unused_4033_ = lean_ctor_get(v_snd_3914_, 1);
lean_dec(v_unused_4033_);
v_unused_4034_ = lean_ctor_get(v_snd_3914_, 0);
lean_dec(v_unused_4034_);
v___x_3942_ = v_snd_3914_;
v_isShared_3943_ = v_isSharedCheck_4031_;
goto v_resetjp_3941_;
}
else
{
lean_dec(v_snd_3914_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_4031_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v_array_3944_; lean_object* v_start_3945_; lean_object* v_stop_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3951_; 
v_array_3944_ = lean_ctor_get(v_fst_3923_, 0);
v_start_3945_ = lean_ctor_get(v_fst_3923_, 1);
v_stop_3946_ = lean_ctor_get(v_fst_3923_, 2);
v___x_3947_ = lean_array_fget(v_array_3927_, v_start_3928_);
v___x_3948_ = lean_unsigned_to_nat(1u);
v___x_3949_ = lean_nat_add(v_start_3928_, v___x_3948_);
lean_dec(v_start_3928_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 1, v___x_3949_);
v___x_3951_ = v___x_3942_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_array_3927_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v___x_3949_);
lean_ctor_set(v_reuseFailAlloc_4030_, 2, v_stop_3929_);
v___x_3951_ = v_reuseFailAlloc_4030_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
uint8_t v___x_3952_; 
v___x_3952_ = lean_nat_dec_lt(v_start_3945_, v_stop_3946_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3954_; 
lean_dec(v___x_3947_);
lean_dec(v_a_3898_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 1, v___x_3951_);
v___x_3954_ = v___x_3925_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_fst_3923_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v___x_3951_);
v___x_3954_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_object* v___x_3956_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 1, v___x_3954_);
v___x_3956_ = v___x_3921_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_fst_3919_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v___x_3954_);
v___x_3956_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
lean_object* v___x_3958_; 
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 1, v___x_3956_);
v___x_3958_ = v___x_3917_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_fst_3915_);
lean_ctor_set(v_reuseFailAlloc_3960_, 1, v___x_3956_);
v___x_3958_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v___x_3959_; 
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
return v___x_3959_;
}
}
}
}
else
{
lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_4026_; 
lean_inc(v_stop_3946_);
lean_inc(v_start_3945_);
lean_inc_ref(v_array_3944_);
v_isSharedCheck_4026_ = !lean_is_exclusive(v_fst_3923_);
if (v_isSharedCheck_4026_ == 0)
{
lean_object* v_unused_4027_; lean_object* v_unused_4028_; lean_object* v_unused_4029_; 
v_unused_4027_ = lean_ctor_get(v_fst_3923_, 2);
lean_dec(v_unused_4027_);
v_unused_4028_ = lean_ctor_get(v_fst_3923_, 1);
lean_dec(v_unused_4028_);
v_unused_4029_ = lean_ctor_get(v_fst_3923_, 0);
lean_dec(v_unused_4029_);
v___x_3964_ = v_fst_3923_;
v_isShared_3965_ = v_isSharedCheck_4026_;
goto v_resetjp_3963_;
}
else
{
lean_dec(v_fst_3923_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_4026_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3966_; lean_object* v___x_3968_; 
v___x_3966_ = lean_nat_add(v_start_3945_, v___x_3948_);
lean_dec(v_start_3945_);
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 1, v___x_3966_);
v___x_3968_ = v___x_3964_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_array_3944_);
lean_ctor_set(v_reuseFailAlloc_4025_, 1, v___x_3966_);
lean_ctor_set(v_reuseFailAlloc_4025_, 2, v_stop_3946_);
v___x_3968_ = v_reuseFailAlloc_4025_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
if (lean_obj_tag(v___x_3947_) == 1)
{
lean_object* v_val_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_4013_; 
v_val_3969_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_3971_ = v___x_3947_;
v_isShared_3972_ = v_isSharedCheck_4013_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_val_3969_);
lean_dec(v___x_3947_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_4013_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3973_ = lean_unsigned_to_nat(0u);
v___x_3974_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_3975_ = lean_box(0);
v___x_3976_ = lean_array_get(v___x_3975_, v_val_3969_, v___x_3973_);
lean_dec(v_val_3969_);
lean_inc(v_a_3898_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 0, v_a_3898_);
v___x_3978_ = v___x_3971_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_3898_);
v___x_3978_ = v_reuseFailAlloc_4012_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
uint8_t v___x_3979_; 
v___x_3979_ = l_Option_instDecidableEq___redArg(v___x_3974_, v___x_3976_, v___x_3978_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
lean_dec_ref(v___x_3968_);
lean_dec_ref(v___x_3951_);
lean_del_object(v___x_3925_);
lean_del_object(v___x_3921_);
lean_dec(v_fst_3919_);
lean_del_object(v___x_3917_);
lean_dec(v_fst_3915_);
v___x_3980_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__2);
v___x_3981_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_3980_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3991_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3984_ = v___x_3981_;
v_isShared_3985_ = v_isSharedCheck_3991_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3981_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3991_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
if (lean_obj_tag(v_a_3982_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3988_; 
lean_dec(v_a_3898_);
v_a_3986_ = lean_ctor_get(v_a_3982_, 0);
lean_inc(v_a_3986_);
lean_dec_ref_known(v_a_3982_, 1);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v_a_3986_);
v___x_3988_ = v___x_3984_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_a_3986_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
else
{
lean_object* v_a_3990_; 
lean_del_object(v___x_3984_);
v_a_3990_ = lean_ctor_get(v_a_3982_, 0);
lean_inc(v_a_3990_);
lean_dec_ref_known(v_a_3982_, 1);
v_a_3906_ = v_a_3990_;
goto v___jp_3905_;
}
}
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
lean_dec(v_a_3898_);
v_a_3992_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3981_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3981_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
else
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4004_; 
lean_inc(v_fst_3919_);
v___x_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4000_, 0, v_fst_3919_);
v___x_4001_ = lean_array_push(v_fst_3915_, v___x_4000_);
v___x_4002_ = lean_nat_add(v_fst_3919_, v___x_3948_);
lean_dec(v_fst_3919_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 1, v___x_3951_);
lean_ctor_set(v___x_3925_, 0, v___x_3968_);
v___x_4004_ = v___x_3925_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_3968_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v___x_3951_);
v___x_4004_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
lean_object* v___x_4006_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 1, v___x_4004_);
lean_ctor_set(v___x_3921_, 0, v___x_4002_);
v___x_4006_ = v___x_3921_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4002_);
lean_ctor_set(v_reuseFailAlloc_4010_, 1, v___x_4004_);
v___x_4006_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
lean_object* v___x_4008_; 
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 1, v___x_4006_);
lean_ctor_set(v___x_3917_, 0, v___x_4001_);
v___x_4008_ = v___x_3917_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_4001_);
lean_ctor_set(v_reuseFailAlloc_4009_, 1, v___x_4006_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
v_a_3906_ = v___x_4008_;
goto v___jp_3905_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4017_; 
lean_dec(v___x_3947_);
v___x_4014_ = lean_box(0);
v___x_4015_ = lean_array_push(v_fst_3915_, v___x_4014_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 1, v___x_3951_);
lean_ctor_set(v___x_3925_, 0, v___x_3968_);
v___x_4017_ = v___x_3925_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v___x_3968_);
lean_ctor_set(v_reuseFailAlloc_4024_, 1, v___x_3951_);
v___x_4017_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
lean_object* v___x_4019_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 1, v___x_4017_);
v___x_4019_ = v___x_3921_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_fst_3919_);
lean_ctor_set(v_reuseFailAlloc_4023_, 1, v___x_4017_);
v___x_4019_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4021_; 
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 1, v___x_4019_);
lean_ctor_set(v___x_3917_, 0, v___x_4015_);
v___x_4021_ = v___x_3917_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4015_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v___x_4019_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
v_a_3906_ = v___x_4021_;
goto v___jp_3905_;
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
}
}
}
v___jp_3905_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = lean_unsigned_to_nat(1u);
v___x_3908_ = lean_nat_add(v_a_3898_, v___x_3907_);
lean_dec(v_a_3898_);
v_a_3898_ = v___x_3908_;
v_b_3899_ = v_a_3906_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4041_, lean_object* v_a_4042_, lean_object* v_b_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4041_, v_a_4042_, v_b_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v_upperBound_4041_);
return v_res_4049_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4052_ = lean_unsigned_to_nat(12u);
v___x_4053_ = lean_unsigned_to_nat(294u);
v___x_4054_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_4055_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4056_ = l_mkPanicMessageWithDecl(v___x_4055_, v___x_4054_, v___x_4053_, v___x_4052_, v___x_4051_);
return v___x_4056_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2));
v___x_4059_ = lean_unsigned_to_nat(12u);
v___x_4060_ = lean_unsigned_to_nat(297u);
v___x_4061_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_4062_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4063_ = l_mkPanicMessageWithDecl(v___x_4062_, v___x_4061_, v___x_4060_, v___x_4059_, v___x_4058_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_4064_, lean_object* v_as_4065_, size_t v_sz_4066_, size_t v_i_4067_, lean_object* v_b_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
lean_object* v_a_4075_; uint8_t v___x_4079_; 
v___x_4079_ = lean_usize_dec_lt(v_i_4067_, v_sz_4066_);
if (v___x_4079_ == 0)
{
lean_object* v___x_4080_; 
v___x_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4080_, 0, v_b_4068_);
return v___x_4080_;
}
else
{
lean_object* v_a_4081_; 
v_a_4081_ = lean_array_uget_borrowed(v_as_4065_, v_i_4067_);
if (lean_obj_tag(v_a_4081_) == 1)
{
lean_object* v_val_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
v_val_4082_ = lean_ctor_get(v_a_4081_, 0);
v___x_4083_ = lean_unsigned_to_nat(0u);
v___x_4084_ = lean_box(0);
v___x_4085_ = lean_array_get_borrowed(v___x_4084_, v_val_4082_, v___x_4083_);
if (lean_obj_tag(v___x_4085_) == 1)
{
lean_object* v_val_4086_; lean_object* v___x_4087_; 
v_val_4086_ = lean_ctor_get(v___x_4085_, 0);
v___x_4087_ = lean_array_get_borrowed(v___x_4084_, v___x_4064_, v_val_4086_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
lean_dec_ref(v_b_4068_);
v___x_4088_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1);
v___x_4089_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_4088_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4099_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4092_ = v___x_4089_;
v_isShared_4093_ = v_isSharedCheck_4099_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4089_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4099_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
if (lean_obj_tag(v_a_4090_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4096_; 
v_a_4094_ = lean_ctor_get(v_a_4090_, 0);
lean_inc(v_a_4094_);
lean_dec_ref_known(v_a_4090_, 1);
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 0, v_a_4094_);
v___x_4096_ = v___x_4092_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4094_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
else
{
lean_object* v_a_4098_; 
lean_del_object(v___x_4092_);
v_a_4098_ = lean_ctor_get(v_a_4090_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v_a_4090_, 1);
v_a_4075_ = v_a_4098_;
goto v___jp_4074_;
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
v_a_4100_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4089_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4089_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
else
{
lean_object* v___x_4108_; 
lean_inc_ref(v___x_4087_);
v___x_4108_ = lean_array_push(v_b_4068_, v___x_4087_);
v_a_4075_ = v___x_4108_;
goto v___jp_4074_;
}
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3);
v___x_4110_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_4109_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_dec_ref_known(v___x_4110_, 1);
v_a_4075_ = v_b_4068_;
goto v___jp_4074_;
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec_ref(v_b_4068_);
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4110_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4110_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
}
else
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4119_ = lean_box(0);
v___x_4120_ = lean_array_push(v_b_4068_, v___x_4119_);
v_a_4075_ = v___x_4120_;
goto v___jp_4074_;
}
}
v___jp_4074_:
{
size_t v___x_4076_; size_t v___x_4077_; 
v___x_4076_ = ((size_t)1ULL);
v___x_4077_ = lean_usize_add(v_i_4067_, v___x_4076_);
v_i_4067_ = v___x_4077_;
v_b_4068_ = v_a_4075_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_4121_, lean_object* v_as_4122_, lean_object* v_sz_4123_, lean_object* v_i_4124_, lean_object* v_b_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
size_t v_sz_boxed_4131_; size_t v_i_boxed_4132_; lean_object* v_res_4133_; 
v_sz_boxed_4131_ = lean_unbox_usize(v_sz_4123_);
lean_dec(v_sz_4123_);
v_i_boxed_4132_ = lean_unbox_usize(v_i_4124_);
lean_dec(v_i_4124_);
v_res_4133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_4121_, v_as_4122_, v_sz_boxed_4131_, v_i_boxed_4132_, v_b_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec_ref(v_as_4122_);
lean_dec_ref(v___x_4121_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_4136_, lean_object* v___x_4137_, lean_object* v___x_4138_, lean_object* v_a_4139_, lean_object* v_b_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
uint8_t v___x_4146_; 
v___x_4146_ = lean_nat_dec_lt(v_a_4139_, v_upperBound_4136_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4147_; 
lean_dec(v_a_4139_);
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v_b_4140_);
return v___x_4147_;
}
else
{
lean_object* v___x_4148_; lean_object* v___x_4149_; size_t v_sz_4150_; size_t v___x_4151_; lean_object* v___x_4152_; 
v___x_4148_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_4149_ = lean_array_fget_borrowed(v___x_4137_, v_a_4139_);
v_sz_4150_ = lean_array_size(v___x_4149_);
v___x_4151_ = ((size_t)0ULL);
v___x_4152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_4138_, v___x_4149_, v_sz_4150_, v___x_4151_, v___x_4148_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4152_, 1);
v___x_4154_ = lean_array_push(v_b_4140_, v_a_4153_);
v___x_4155_ = lean_unsigned_to_nat(1u);
v___x_4156_ = lean_nat_add(v_a_4139_, v___x_4155_);
lean_dec(v_a_4139_);
v_a_4139_ = v___x_4156_;
v_b_4140_ = v___x_4154_;
goto _start;
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec_ref(v_b_4140_);
lean_dec(v_a_4139_);
v_a_4158_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4152_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4152_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_4166_, lean_object* v___x_4167_, lean_object* v___x_4168_, lean_object* v_a_4169_, lean_object* v_b_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4166_, v___x_4167_, v___x_4168_, v_a_4169_, v_b_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec_ref(v___x_4168_);
lean_dec_ref(v___x_4167_);
lean_dec(v_upperBound_4166_);
return v_res_4176_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4178_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4179_ = lean_unsigned_to_nat(4u);
v___x_4180_ = lean_unsigned_to_nat(275u);
v___x_4181_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_4182_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4183_ = l_mkPanicMessageWithDecl(v___x_4182_, v___x_4181_, v___x_4180_, v___x_4179_, v___x_4178_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4184_, lean_object* v___x_4185_, lean_object* v___x_4186_, lean_object* v_xs_4187_, lean_object* v_x_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v_graph_4194_; lean_object* v_revDeps_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4248_; 
v_graph_4194_ = lean_ctor_get(v_a_4184_, 0);
v_revDeps_4195_ = lean_ctor_get(v_a_4184_, 1);
v_isSharedCheck_4248_ = !lean_is_exclusive(v_a_4184_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4197_ = v_a_4184_;
v_isShared_4198_ = v_isSharedCheck_4248_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_revDeps_4195_);
lean_inc(v_graph_4194_);
lean_dec(v_a_4184_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4248_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; uint8_t v___x_4202_; 
v___x_4199_ = lean_array_get_borrowed(v___x_4185_, v_graph_4194_, v___x_4186_);
v___x_4200_ = lean_array_get_size(v_xs_4187_);
v___x_4201_ = lean_array_get_size(v___x_4199_);
v___x_4202_ = lean_nat_dec_eq(v___x_4200_, v___x_4201_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_del_object(v___x_4197_);
lean_dec_ref(v_revDeps_4195_);
lean_dec_ref(v_graph_4194_);
lean_dec_ref(v_xs_4187_);
lean_dec(v___x_4186_);
v___x_4203_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4204_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4203_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4204_;
}
else
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4209_; 
v___x_4205_ = lean_mk_empty_array_with_capacity(v___x_4186_);
lean_inc_n(v___x_4186_, 2);
v___x_4206_ = l_Array_toSubarray___redArg(v_xs_4187_, v___x_4186_, v___x_4200_);
lean_inc(v___x_4199_);
v___x_4207_ = l_Array_toSubarray___redArg(v___x_4199_, v___x_4186_, v___x_4201_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 1, v___x_4207_);
lean_ctor_set(v___x_4197_, 0, v___x_4206_);
v___x_4209_ = v___x_4197_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v___x_4206_);
lean_ctor_set(v_reuseFailAlloc_4247_, 1, v___x_4207_);
v___x_4209_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
lean_inc(v___x_4186_);
v___x_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4186_);
lean_ctor_set(v___x_4210_, 1, v___x_4209_);
v___x_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4205_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
v___x_4212_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4200_, v___x_4186_, v___x_4211_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v_snd_4214_; lean_object* v_fst_4215_; lean_object* v_fst_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4212_, 1);
v_snd_4214_ = lean_ctor_get(v_a_4213_, 1);
lean_inc(v_snd_4214_);
v_fst_4215_ = lean_ctor_get(v_a_4213_, 0);
lean_inc_n(v_fst_4215_, 2);
lean_dec(v_a_4213_);
v_fst_4216_ = lean_ctor_get(v_snd_4214_, 0);
lean_inc(v_fst_4216_);
lean_dec(v_snd_4214_);
v___x_4217_ = lean_unsigned_to_nat(1u);
v___x_4218_ = lean_array_get_size(v_graph_4194_);
v___x_4219_ = lean_mk_empty_array_with_capacity(v___x_4217_);
v___x_4220_ = lean_array_push(v___x_4219_, v_fst_4215_);
v___x_4221_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4218_, v_graph_4194_, v_fst_4215_, v___x_4217_, v___x_4220_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec(v_fst_4215_);
lean_dec_ref(v_graph_4194_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4230_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4224_ = v___x_4221_;
v_isShared_4225_ = v_isSharedCheck_4230_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4221_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4230_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4226_; lean_object* v___x_4228_; 
v___x_4226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4226_, 0, v_fst_4216_);
lean_ctor_set(v___x_4226_, 1, v_a_4222_);
lean_ctor_set(v___x_4226_, 2, v_revDeps_4195_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v___x_4226_);
v___x_4228_ = v___x_4224_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4226_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_dec(v_fst_4216_);
lean_dec_ref(v_revDeps_4195_);
v_a_4231_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___x_4221_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4221_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
lean_dec_ref(v_revDeps_4195_);
lean_dec_ref(v_graph_4194_);
v_a_4239_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4212_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4212_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4249_, lean_object* v___x_4250_, lean_object* v___x_4251_, lean_object* v_xs_4252_, lean_object* v_x_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4249_, v___x_4250_, v___x_4251_, v_xs_4252_, v_x_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec_ref(v_x_4253_);
lean_dec_ref(v___x_4250_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_){
_start:
{
lean_object* v___x_4266_; 
lean_inc_ref(v_preDefs_4260_);
v___x_4266_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v_value_4271_; lean_object* v___x_4272_; lean_object* v___f_4273_; uint8_t v___x_4274_; lean_object* v___x_4275_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref_known(v___x_4266_, 1);
v___x_4268_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4269_ = lean_unsigned_to_nat(0u);
v___x_4270_ = lean_array_get(v___x_4268_, v_preDefs_4260_, v___x_4269_);
lean_dec_ref(v_preDefs_4260_);
v_value_4271_ = lean_ctor_get(v___x_4270_, 7);
lean_inc_ref(v_value_4271_);
lean_dec(v___x_4270_);
v___x_4272_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4273_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4273_, 0, v_a_4267_);
lean_closure_set(v___f_4273_, 1, v___x_4272_);
lean_closure_set(v___f_4273_, 2, v___x_4269_);
v___x_4274_ = 0;
v___x_4275_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4271_, v___f_4273_, v___x_4274_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
return v___x_4275_;
}
else
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
lean_dec_ref(v_preDefs_4260_);
v_a_4276_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4266_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4266_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
lean_dec(v_a_4288_);
lean_dec_ref(v_a_4287_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4291_, lean_object* v___x_4292_, lean_object* v___x_4293_, lean_object* v_inst_4294_, lean_object* v_R_4295_, lean_object* v_a_4296_, lean_object* v_b_4297_, lean_object* v_c_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4291_, v___x_4292_, v___x_4293_, v_a_4296_, v_b_4297_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4305_, lean_object* v___x_4306_, lean_object* v___x_4307_, lean_object* v_inst_4308_, lean_object* v_R_4309_, lean_object* v_a_4310_, lean_object* v_b_4311_, lean_object* v_c_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4305_, v___x_4306_, v___x_4307_, v_inst_4308_, v_R_4309_, v_a_4310_, v_b_4311_, v_c_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec_ref(v___x_4307_);
lean_dec_ref(v___x_4306_);
lean_dec(v_upperBound_4305_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4319_, lean_object* v_inst_4320_, lean_object* v_R_4321_, lean_object* v_a_4322_, lean_object* v_b_4323_, lean_object* v_c_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4319_, v_a_4322_, v_b_4323_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4331_, lean_object* v_inst_4332_, lean_object* v_R_4333_, lean_object* v_a_4334_, lean_object* v_b_4335_, lean_object* v_c_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4331_, v_inst_4332_, v_R_4333_, v_a_4334_, v_b_4335_, v_c_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v_upperBound_4331_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4343_, size_t v_i_4344_, size_t v_stop_4345_, lean_object* v_b_4346_){
_start:
{
uint8_t v___x_4347_; 
v___x_4347_ = lean_usize_dec_eq(v_i_4344_, v_stop_4345_);
if (v___x_4347_ == 0)
{
size_t v___x_4348_; size_t v___x_4349_; lean_object* v___x_4350_; 
v___x_4348_ = ((size_t)1ULL);
v___x_4349_ = lean_usize_sub(v_i_4344_, v___x_4348_);
v___x_4350_ = lean_array_uget_borrowed(v_as_4343_, v___x_4349_);
if (lean_obj_tag(v___x_4350_) == 0)
{
v_i_4344_ = v___x_4349_;
goto _start;
}
else
{
lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4352_ = lean_unsigned_to_nat(1u);
v___x_4353_ = lean_nat_add(v_b_4346_, v___x_4352_);
lean_dec(v_b_4346_);
v_i_4344_ = v___x_4349_;
v_b_4346_ = v___x_4353_;
goto _start;
}
}
else
{
return v_b_4346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4355_, lean_object* v_i_4356_, lean_object* v_stop_4357_, lean_object* v_b_4358_){
_start:
{
size_t v_i_boxed_4359_; size_t v_stop_boxed_4360_; lean_object* v_res_4361_; 
v_i_boxed_4359_ = lean_unbox_usize(v_i_4356_);
lean_dec(v_i_4356_);
v_stop_boxed_4360_ = lean_unbox_usize(v_stop_4357_);
lean_dec(v_stop_4357_);
v_res_4361_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4355_, v_i_boxed_4359_, v_stop_boxed_4360_, v_b_4358_);
lean_dec_ref(v_as_4355_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4362_){
_start:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; 
v___x_4363_ = lean_unsigned_to_nat(0u);
v___x_4364_ = lean_array_get_size(v_perm_4362_);
v___x_4365_ = lean_nat_dec_lt(v___x_4363_, v___x_4364_);
if (v___x_4365_ == 0)
{
return v___x_4363_;
}
else
{
size_t v___x_4366_; size_t v___x_4367_; lean_object* v___x_4368_; 
v___x_4366_ = lean_usize_of_nat(v___x_4364_);
v___x_4367_ = ((size_t)0ULL);
v___x_4368_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4362_, v___x_4366_, v___x_4367_, v___x_4363_);
return v___x_4368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4369_);
lean_dec_ref(v_perm_4369_);
return v_res_4370_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4371_, lean_object* v_i_4372_){
_start:
{
lean_object* v___x_4373_; uint8_t v___x_4374_; 
v___x_4373_ = lean_array_get_size(v_perm_4371_);
v___x_4374_ = lean_nat_dec_lt(v_i_4372_, v___x_4373_);
if (v___x_4374_ == 0)
{
return v___x_4374_;
}
else
{
lean_object* v___x_4375_; 
v___x_4375_ = lean_array_fget_borrowed(v_perm_4371_, v_i_4372_);
if (lean_obj_tag(v___x_4375_) == 0)
{
uint8_t v___x_4376_; 
v___x_4376_ = 0;
return v___x_4376_;
}
else
{
return v___x_4374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4377_, lean_object* v_i_4378_){
_start:
{
uint8_t v_res_4379_; lean_object* v_r_4380_; 
v_res_4379_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4377_, v_i_4378_);
lean_dec(v_i_4378_);
lean_dec_ref(v_perm_4377_);
v_r_4380_ = lean_box(v_res_4379_);
return v_r_4380_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v___f_4387_; lean_object* v___x_1072__overap_4388_; lean_object* v___x_4389_; 
v___f_4387_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_1072__overap_4388_ = lean_panic_fn_borrowed(v___f_4387_, v_msg_4381_);
lean_inc(v___y_4385_);
lean_inc_ref(v___y_4384_);
lean_inc(v___y_4383_);
lean_inc_ref(v___y_4382_);
v___x_4389_ = lean_apply_5(v___x_1072__overap_4388_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, lean_box(0));
return v___x_4389_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4397_, lean_object* v_msg_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v___x_4404_; 
v___x_4404_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
return v___x_4404_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4405_, lean_object* v_msg_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4405_, v_msg_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4413_, lean_object* v_maxFVars_x3f_4414_, lean_object* v_k_4415_, uint8_t v_cleanupAnnotations_4416_, uint8_t v_whnfType_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v___f_4423_; lean_object* v___x_4424_; 
v___f_4423_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4423_, 0, v_k_4415_);
v___x_4424_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4413_, v_maxFVars_x3f_4414_, v___f_4423_, v_cleanupAnnotations_4416_, v_whnfType_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4424_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4424_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
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
v_a_4433_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4424_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4424_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4441_, lean_object* v_maxFVars_x3f_4442_, lean_object* v_k_4443_, lean_object* v_cleanupAnnotations_4444_, lean_object* v_whnfType_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4451_; uint8_t v_whnfType_boxed_4452_; lean_object* v_res_4453_; 
v_cleanupAnnotations_boxed_4451_ = lean_unbox(v_cleanupAnnotations_4444_);
v_whnfType_boxed_4452_ = lean_unbox(v_whnfType_4445_);
v_res_4453_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4441_, v_maxFVars_x3f_4442_, v_k_4443_, v_cleanupAnnotations_boxed_4451_, v_whnfType_boxed_4452_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4454_, lean_object* v_type_4455_, lean_object* v_maxFVars_x3f_4456_, lean_object* v_k_4457_, uint8_t v_cleanupAnnotations_4458_, uint8_t v_whnfType_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v___x_4465_; 
v___x_4465_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4455_, v_maxFVars_x3f_4456_, v_k_4457_, v_cleanupAnnotations_4458_, v_whnfType_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4466_, lean_object* v_type_4467_, lean_object* v_maxFVars_x3f_4468_, lean_object* v_k_4469_, lean_object* v_cleanupAnnotations_4470_, lean_object* v_whnfType_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4477_; uint8_t v_whnfType_boxed_4478_; lean_object* v_res_4479_; 
v_cleanupAnnotations_boxed_4477_ = lean_unbox(v_cleanupAnnotations_4470_);
v_whnfType_boxed_4478_ = lean_unbox(v_whnfType_4471_);
v_res_4479_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4466_, v_type_4467_, v_maxFVars_x3f_4468_, v_k_4469_, v_cleanupAnnotations_boxed_4477_, v_whnfType_boxed_4478_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
return v_res_4479_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4482_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4483_ = lean_unsigned_to_nat(6u);
v___x_4484_ = lean_unsigned_to_nat(329u);
v___x_4485_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4486_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4487_ = l_mkPanicMessageWithDecl(v___x_4486_, v___x_4485_, v___x_4484_, v___x_4483_, v___x_4482_);
return v___x_4487_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4491_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4492_ = lean_unsigned_to_nat(8u);
v___x_4493_ = lean_unsigned_to_nat(322u);
v___x_4494_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4495_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4496_ = l_mkPanicMessageWithDecl(v___x_4495_, v___x_4494_, v___x_4493_, v___x_4492_, v___x_4491_);
return v___x_4496_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4498_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4499_ = lean_unsigned_to_nat(8u);
v___x_4500_ = lean_unsigned_to_nat(325u);
v___x_4501_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4502_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4503_ = l_mkPanicMessageWithDecl(v___x_4502_, v___x_4501_, v___x_4500_, v___x_4499_, v___x_4498_);
return v___x_4503_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4505_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4506_ = lean_unsigned_to_nat(8u);
v___x_4507_ = lean_unsigned_to_nat(324u);
v___x_4508_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4509_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4510_ = l_mkPanicMessageWithDecl(v___x_4509_, v___x_4508_, v___x_4507_, v___x_4506_, v___x_4505_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4511_, lean_object* v_xs_4512_, lean_object* v_val_4513_, lean_object* v_i_4514_, lean_object* v_perm_4515_, lean_object* v_k_4516_, lean_object* v_xs_x27_4517_, lean_object* v_type_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v___x_4524_; uint8_t v___x_4525_; 
v___x_4524_ = lean_array_get_size(v_xs_x27_4517_);
v___x_4525_ = lean_nat_dec_eq(v___x_4524_, v___x_4511_);
if (v___x_4525_ == 0)
{
lean_object* v___x_4526_; lean_object* v___x_4527_; 
lean_dec_ref(v_type_4518_);
lean_dec_ref(v_k_4516_);
lean_dec_ref(v_perm_4515_);
lean_dec_ref(v_xs_4512_);
v___x_4526_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4527_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4526_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
return v___x_4527_;
}
else
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v_x_4530_; lean_object* v___x_4531_; 
v___x_4528_ = l_Lean_instInhabitedExpr;
v___x_4529_ = lean_unsigned_to_nat(0u);
v_x_4530_ = lean_array_get_borrowed(v___x_4528_, v_xs_x27_4517_, v___x_4529_);
lean_inc(v___y_4522_);
lean_inc_ref(v___y_4521_);
lean_inc(v___y_4520_);
lean_inc_ref(v___y_4519_);
lean_inc(v_x_4530_);
v___x_4531_ = lean_infer_type(v_x_4530_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; uint8_t v___x_4533_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref_known(v___x_4531_, 1);
v___x_4533_ = l_Lean_Expr_hasLooseBVars(v_a_4532_);
lean_dec(v_a_4532_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4534_ = lean_array_get_size(v_xs_4512_);
v___x_4535_ = lean_nat_dec_lt(v_val_4513_, v___x_4534_);
if (v___x_4535_ == 0)
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
lean_dec_ref(v_type_4518_);
lean_dec_ref(v_k_4516_);
lean_dec_ref(v_perm_4515_);
lean_dec_ref(v_xs_4512_);
v___x_4536_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4537_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4536_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
return v___x_4537_;
}
else
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4538_ = lean_nat_add(v_i_4514_, v___x_4511_);
lean_inc(v_x_4530_);
v___x_4539_ = lean_array_set(v_xs_4512_, v_val_4513_, v_x_4530_);
v___x_4540_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4515_, v_k_4516_, v___x_4538_, v_type_4518_, v___x_4539_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
return v___x_4540_;
}
}
else
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
lean_dec_ref(v_type_4518_);
lean_dec_ref(v_k_4516_);
lean_dec_ref(v_perm_4515_);
lean_dec_ref(v_xs_4512_);
v___x_4541_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4542_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4541_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
return v___x_4542_;
}
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
lean_dec_ref(v_type_4518_);
lean_dec_ref(v_k_4516_);
lean_dec_ref(v_perm_4515_);
lean_dec_ref(v_xs_4512_);
v_a_4543_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4531_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4531_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4551_, lean_object* v_xs_4552_, lean_object* v_val_4553_, lean_object* v_i_4554_, lean_object* v_perm_4555_, lean_object* v_k_4556_, lean_object* v_xs_x27_4557_, lean_object* v_type_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v_res_4564_; 
v_res_4564_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4551_, v_xs_4552_, v_val_4553_, v_i_4554_, v_perm_4555_, v_k_4556_, v_xs_x27_4557_, v_type_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec_ref(v_xs_x27_4557_);
lean_dec(v_i_4554_);
lean_dec(v_val_4553_);
lean_dec(v___x_4551_);
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4565_, lean_object* v_k_4566_, lean_object* v_i_4567_, lean_object* v_type_4568_, lean_object* v_xs_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v___x_4575_; uint8_t v___x_4576_; 
v___x_4575_ = lean_array_get_size(v_perm_4565_);
v___x_4576_ = lean_nat_dec_lt(v_i_4567_, v___x_4575_);
if (v___x_4576_ == 0)
{
lean_object* v___x_4577_; 
lean_dec_ref(v_type_4568_);
lean_dec(v_i_4567_);
lean_dec_ref(v_perm_4565_);
lean_inc(v_a_4573_);
lean_inc_ref(v_a_4572_);
lean_inc(v_a_4571_);
lean_inc_ref(v_a_4570_);
v___x_4577_ = lean_apply_6(v_k_4566_, v_xs_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_, lean_box(0));
return v___x_4577_;
}
else
{
lean_object* v___x_4578_; 
v___x_4578_ = lean_array_fget_borrowed(v_perm_4565_, v_i_4567_);
if (lean_obj_tag(v___x_4578_) == 0)
{
lean_object* v___x_4579_; 
lean_inc(v_a_4573_);
lean_inc_ref(v_a_4572_);
lean_inc(v_a_4571_);
lean_inc_ref(v_a_4570_);
v___x_4579_ = lean_whnf(v_type_4568_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; uint8_t v___x_4581_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
lean_dec_ref_known(v___x_4579_, 1);
v___x_4581_ = l_Lean_Expr_isForall(v_a_4580_);
if (v___x_4581_ == 0)
{
lean_object* v___x_4582_; lean_object* v___x_4583_; 
lean_dec(v_a_4580_);
lean_dec_ref(v_xs_4569_);
lean_dec(v_i_4567_);
lean_dec_ref(v_k_4566_);
lean_dec_ref(v_perm_4565_);
v___x_4582_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4583_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4582_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_);
return v___x_4583_;
}
else
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4584_ = lean_unsigned_to_nat(1u);
v___x_4585_ = lean_nat_add(v_i_4567_, v___x_4584_);
lean_dec(v_i_4567_);
v___x_4586_ = l_Lean_Expr_bindingBody_x21(v_a_4580_);
lean_dec(v_a_4580_);
v_i_4567_ = v___x_4585_;
v_type_4568_ = v___x_4586_;
goto _start;
}
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4595_; 
lean_dec_ref(v_xs_4569_);
lean_dec(v_i_4567_);
lean_dec_ref(v_k_4566_);
lean_dec_ref(v_perm_4565_);
v_a_4588_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v___x_4579_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4579_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4593_; 
if (v_isShared_4591_ == 0)
{
v___x_4593_ = v___x_4590_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
else
{
lean_object* v_val_4596_; lean_object* v___x_4597_; lean_object* v___f_4598_; lean_object* v___x_4599_; uint8_t v___x_4600_; lean_object* v___x_4601_; 
v_val_4596_ = lean_ctor_get(v___x_4578_, 0);
lean_inc(v_val_4596_);
v___x_4597_ = lean_unsigned_to_nat(1u);
v___f_4598_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4598_, 0, v___x_4597_);
lean_closure_set(v___f_4598_, 1, v_xs_4569_);
lean_closure_set(v___f_4598_, 2, v_val_4596_);
lean_closure_set(v___f_4598_, 3, v_i_4567_);
lean_closure_set(v___f_4598_, 4, v_perm_4565_);
lean_closure_set(v___f_4598_, 5, v_k_4566_);
v___x_4599_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4600_ = 0;
v___x_4601_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4568_, v___x_4599_, v___f_4598_, v___x_4576_, v___x_4600_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_);
return v___x_4601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4602_, lean_object* v_k_4603_, lean_object* v_i_4604_, lean_object* v_type_4605_, lean_object* v_xs_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4602_, v_k_4603_, v_i_4604_, v_type_4605_, v_xs_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_);
lean_dec(v_a_4610_);
lean_dec_ref(v_a_4609_);
lean_dec(v_a_4608_);
lean_dec_ref(v_a_4607_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4613_, lean_object* v_perm_4614_, lean_object* v_k_4615_, lean_object* v_i_4616_, lean_object* v_type_4617_, lean_object* v_xs_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_){
_start:
{
lean_object* v___x_4624_; 
v___x_4624_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4614_, v_k_4615_, v_i_4616_, v_type_4617_, v_xs_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4625_, lean_object* v_perm_4626_, lean_object* v_k_4627_, lean_object* v_i_4628_, lean_object* v_type_4629_, lean_object* v_xs_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4625_, v_perm_4626_, v_k_4627_, v_i_4628_, v_type_4629_, v_xs_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_);
lean_dec(v_a_4634_);
lean_dec_ref(v_a_4633_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
return v_res_4636_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4637_ = lean_unsigned_to_nat(0u);
v___x_4638_ = l_Lean_Level_ofNat(v___x_4637_);
return v___x_4638_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4640_ = l_Lean_mkSort(v___x_4639_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4641_, lean_object* v_type_4642_, lean_object* v_k_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4649_ = lean_unsigned_to_nat(0u);
v___x_4650_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4641_);
v___x_4651_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4652_ = lean_mk_array(v___x_4650_, v___x_4651_);
v___x_4653_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4641_, v_k_4643_, v___x_4649_, v_type_4642_, v___x_4652_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4654_, lean_object* v_type_4655_, lean_object* v_k_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4654_, v_type_4655_, v_k_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
lean_dec(v_a_4658_);
lean_dec_ref(v_a_4657_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4663_, lean_object* v_perm_4664_, lean_object* v_type_4665_, lean_object* v_k_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_){
_start:
{
lean_object* v___x_4672_; 
v___x_4672_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4664_, v_type_4665_, v_k_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4673_, lean_object* v_perm_4674_, lean_object* v_type_4675_, lean_object* v_k_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4673_, v_perm_4674_, v_type_4675_, v_k_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4683_, lean_object* v_runInBase_4684_, lean_object* v_b_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4691_ = lean_apply_1(v_k_4683_, v_b_4685_);
lean_inc(v___y_4689_);
lean_inc_ref(v___y_4688_);
lean_inc(v___y_4687_);
lean_inc_ref(v___y_4686_);
v___x_4692_ = lean_apply_7(v_runInBase_4684_, lean_box(0), v___x_4691_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, lean_box(0));
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4693_, lean_object* v_runInBase_4694_, lean_object* v_b_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4693_, v_runInBase_4694_, v_b_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4702_, lean_object* v_perm_4703_, lean_object* v_type_4704_, lean_object* v_runInBase_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v___f_4711_; lean_object* v___x_4712_; 
v___f_4711_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4711_, 0, v_k_4702_);
lean_closure_set(v___f_4711_, 1, v_runInBase_4705_);
v___x_4712_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4703_, v_type_4704_, v___f_4711_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4713_, lean_object* v_perm_4714_, lean_object* v_type_4715_, lean_object* v_runInBase_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v_res_4722_; 
v_res_4722_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4713_, v_perm_4714_, v_type_4715_, v_runInBase_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4723_, lean_object* v_inst_4724_, lean_object* v_perm_4725_, lean_object* v_type_4726_, lean_object* v_k_4727_){
_start:
{
lean_object* v_toBind_4728_; lean_object* v_liftWith_4729_; lean_object* v_restoreM_4730_; lean_object* v___f_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; 
v_toBind_4728_ = lean_ctor_get(v_inst_4724_, 1);
lean_inc(v_toBind_4728_);
lean_dec_ref(v_inst_4724_);
v_liftWith_4729_ = lean_ctor_get(v_inst_4723_, 0);
lean_inc(v_liftWith_4729_);
v_restoreM_4730_ = lean_ctor_get(v_inst_4723_, 1);
lean_inc(v_restoreM_4730_);
lean_dec_ref(v_inst_4723_);
v___f_4731_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4731_, 0, v_k_4727_);
lean_closure_set(v___f_4731_, 1, v_perm_4725_);
lean_closure_set(v___f_4731_, 2, v_type_4726_);
v___x_4732_ = lean_apply_2(v_liftWith_4729_, lean_box(0), v___f_4731_);
v___x_4733_ = lean_apply_1(v_restoreM_4730_, lean_box(0));
v___x_4734_ = lean_apply_4(v_toBind_4728_, lean_box(0), lean_box(0), v___x_4732_, v___x_4733_);
return v___x_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4735_, lean_object* v_00_u03b1_4736_, lean_object* v_inst_4737_, lean_object* v_inst_4738_, lean_object* v_perm_4739_, lean_object* v_type_4740_, lean_object* v_k_4741_){
_start:
{
lean_object* v___x_4742_; 
v___x_4742_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4737_, v_inst_4738_, v_perm_4739_, v_type_4740_, v_k_4741_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_){
_start:
{
lean_object* v___f_4749_; lean_object* v___x_603__overap_4750_; lean_object* v___x_4751_; 
v___f_4749_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_603__overap_4750_ = lean_panic_fn_borrowed(v___f_4749_, v_msg_4743_);
lean_inc(v___y_4747_);
lean_inc_ref(v___y_4746_);
lean_inc(v___y_4745_);
lean_inc_ref(v___y_4744_);
v___x_4751_ = lean_apply_5(v___x_603__overap_4750_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, lean_box(0));
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
lean_dec(v___y_4756_);
lean_dec_ref(v___y_4755_);
lean_dec(v___y_4754_);
lean_dec_ref(v___y_4753_);
return v_res_4758_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4761_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4762_ = lean_unsigned_to_nat(10u);
v___x_4763_ = lean_unsigned_to_nat(353u);
v___x_4764_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4765_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4766_ = l_mkPanicMessageWithDecl(v___x_4765_, v___x_4764_, v___x_4763_, v___x_4762_, v___x_4761_);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4767_, lean_object* v_xs_4768_, lean_object* v_tail_4769_, lean_object* v_ys_4770_, lean_object* v_type_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4767_, v_xs_4768_, v_tail_4769_, v_ys_4770_, v_type_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_);
lean_dec(v___y_4775_);
lean_dec_ref(v___y_4774_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
lean_dec_ref(v_ys_4770_);
lean_dec(v___x_4767_);
return v_res_4777_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4778_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4779_ = lean_unsigned_to_nat(8u);
v___x_4780_ = lean_unsigned_to_nat(349u);
v___x_4781_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4782_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4783_ = l_mkPanicMessageWithDecl(v___x_4782_, v___x_4781_, v___x_4780_, v___x_4779_, v___x_4778_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4784_, lean_object* v_x_4785_, lean_object* v_x_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_){
_start:
{
if (lean_obj_tag(v_x_4785_) == 0)
{
lean_object* v___x_4792_; 
lean_dec_ref(v_xs_4784_);
v___x_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4792_, 0, v_x_4786_);
return v___x_4792_;
}
else
{
lean_object* v_head_4793_; 
v_head_4793_ = lean_ctor_get(v_x_4785_, 0);
if (lean_obj_tag(v_head_4793_) == 0)
{
lean_object* v_tail_4794_; lean_object* v___x_4795_; lean_object* v___f_4796_; lean_object* v___x_4797_; uint8_t v___x_4798_; lean_object* v___x_4799_; 
v_tail_4794_ = lean_ctor_get(v_x_4785_, 1);
lean_inc(v_tail_4794_);
lean_dec_ref_known(v_x_4785_, 2);
v___x_4795_ = lean_unsigned_to_nat(1u);
v___f_4796_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4796_, 0, v___x_4795_);
lean_closure_set(v___f_4796_, 1, v_xs_4784_);
lean_closure_set(v___f_4796_, 2, v_tail_4794_);
v___x_4797_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4798_ = 0;
v___x_4799_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4786_, v___x_4797_, v___f_4796_, v___x_4798_, v___x_4798_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_);
return v___x_4799_;
}
else
{
lean_object* v_tail_4800_; lean_object* v_val_4801_; lean_object* v___x_4802_; uint8_t v___x_4803_; 
lean_inc_ref(v_head_4793_);
v_tail_4800_ = lean_ctor_get(v_x_4785_, 1);
lean_inc(v_tail_4800_);
lean_dec_ref_known(v_x_4785_, 2);
v_val_4801_ = lean_ctor_get(v_head_4793_, 0);
lean_inc(v_val_4801_);
lean_dec_ref_known(v_head_4793_, 1);
v___x_4802_ = lean_array_get_size(v_xs_4784_);
v___x_4803_ = lean_nat_dec_lt(v_val_4801_, v___x_4802_);
if (v___x_4803_ == 0)
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
lean_dec(v_val_4801_);
lean_dec(v_tail_4800_);
lean_dec_ref(v_x_4786_);
lean_dec_ref(v_xs_4784_);
v___x_4804_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4805_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4804_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_);
return v___x_4805_;
}
else
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; 
v___x_4806_ = l_Lean_instInhabitedExpr;
v___x_4807_ = lean_array_get_borrowed(v___x_4806_, v_xs_4784_, v_val_4801_);
lean_dec(v_val_4801_);
v___x_4808_ = lean_unsigned_to_nat(1u);
v___x_4809_ = lean_mk_empty_array_with_capacity(v___x_4808_);
lean_inc(v___x_4807_);
v___x_4810_ = lean_array_push(v___x_4809_, v___x_4807_);
v___x_4811_ = l_Lean_Meta_instantiateForall(v_x_4786_, v___x_4810_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_);
lean_dec_ref(v___x_4810_);
if (lean_obj_tag(v___x_4811_) == 0)
{
lean_object* v_a_4812_; 
v_a_4812_ = lean_ctor_get(v___x_4811_, 0);
lean_inc(v_a_4812_);
lean_dec_ref_known(v___x_4811_, 1);
v_x_4785_ = v_tail_4800_;
v_x_4786_ = v_a_4812_;
goto _start;
}
else
{
lean_dec(v_tail_4800_);
lean_dec_ref(v_xs_4784_);
return v___x_4811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4814_, lean_object* v_xs_4815_, lean_object* v_tail_4816_, lean_object* v_ys_4817_, lean_object* v_type_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_){
_start:
{
lean_object* v___x_4824_; uint8_t v___x_4825_; 
v___x_4824_ = lean_array_get_size(v_ys_4817_);
v___x_4825_ = lean_nat_dec_eq(v___x_4824_, v___x_4814_);
if (v___x_4825_ == 0)
{
lean_object* v___x_4826_; lean_object* v___x_4827_; 
lean_dec_ref(v_type_4818_);
lean_dec(v_tail_4816_);
lean_dec_ref(v_xs_4815_);
v___x_4826_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4827_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4826_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
return v___x_4827_;
}
else
{
lean_object* v___x_4828_; 
v___x_4828_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4815_, v_tail_4816_, v_type_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v_a_4829_; uint8_t v___x_4830_; uint8_t v___x_4831_; lean_object* v___x_4832_; 
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4829_);
lean_dec_ref_known(v___x_4828_, 1);
v___x_4830_ = 0;
v___x_4831_ = 1;
v___x_4832_ = l_Lean_Meta_mkForallFVars(v_ys_4817_, v_a_4829_, v___x_4830_, v___x_4825_, v___x_4825_, v___x_4831_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
return v___x_4832_;
}
else
{
return v___x_4828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4833_, lean_object* v_x_4834_, lean_object* v_x_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4833_, v_x_4834_, v_x_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
lean_dec(v_a_4837_);
lean_dec_ref(v_a_4836_);
return v_res_4841_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4844_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4845_ = lean_unsigned_to_nat(2u);
v___x_4846_ = lean_unsigned_to_nat(343u);
v___x_4847_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4848_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4849_ = l_mkPanicMessageWithDecl(v___x_4848_, v___x_4847_, v___x_4846_, v___x_4845_, v___x_4844_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4850_, lean_object* v_type_u2080_4851_, lean_object* v_xs_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_){
_start:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; uint8_t v___x_4860_; 
v___x_4858_ = lean_array_get_size(v_xs_4852_);
v___x_4859_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4850_);
v___x_4860_ = lean_nat_dec_eq(v___x_4858_, v___x_4859_);
lean_dec(v___x_4859_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4861_; lean_object* v___x_4862_; 
lean_dec_ref(v_xs_4852_);
lean_dec_ref(v_type_u2080_4851_);
lean_dec_ref(v_perm_4850_);
v___x_4861_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4862_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4861_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_);
return v___x_4862_;
}
else
{
lean_object* v_mask_4863_; lean_object* v___x_4864_; 
v_mask_4863_ = lean_array_to_list(v_perm_4850_);
v___x_4864_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4852_, v_mask_4863_, v_type_u2080_4851_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_);
return v___x_4864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4865_, lean_object* v_type_u2080_4866_, lean_object* v_xs_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_){
_start:
{
lean_object* v_res_4873_; 
v_res_4873_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4865_, v_type_u2080_4866_, v_xs_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
lean_dec(v_a_4871_);
lean_dec_ref(v_a_4870_);
lean_dec(v_a_4869_);
lean_dec_ref(v_a_4868_);
return v_res_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4874_, lean_object* v_maxFVars_4875_, lean_object* v_k_4876_, uint8_t v_cleanupAnnotations_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
lean_object* v___f_4883_; uint8_t v___x_4884_; uint8_t v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___f_4883_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4883_, 0, v_k_4876_);
v___x_4884_ = 1;
v___x_4885_ = 0;
v___x_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4886_, 0, v_maxFVars_4875_);
v___x_4887_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4874_, v___x_4884_, v___x_4885_, v___x_4884_, v___x_4885_, v___x_4886_, v___f_4883_, v_cleanupAnnotations_4877_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_);
lean_dec_ref_known(v___x_4886_, 1);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4895_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4890_ = v___x_4887_;
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4887_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4893_; 
if (v_isShared_4891_ == 0)
{
v___x_4893_ = v___x_4890_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
else
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
v_a_4896_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___x_4887_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4887_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4904_, lean_object* v_maxFVars_4905_, lean_object* v_k_4906_, lean_object* v_cleanupAnnotations_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4913_; lean_object* v_res_4914_; 
v_cleanupAnnotations_boxed_4913_ = lean_unbox(v_cleanupAnnotations_4907_);
v_res_4914_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4904_, v_maxFVars_4905_, v_k_4906_, v_cleanupAnnotations_boxed_4913_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_);
lean_dec(v___y_4911_);
lean_dec_ref(v___y_4910_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4915_, lean_object* v_e_4916_, lean_object* v_maxFVars_4917_, lean_object* v_k_4918_, uint8_t v_cleanupAnnotations_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
lean_object* v___x_4925_; 
v___x_4925_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4916_, v_maxFVars_4917_, v_k_4918_, v_cleanupAnnotations_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
return v___x_4925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4926_, lean_object* v_e_4927_, lean_object* v_maxFVars_4928_, lean_object* v_k_4929_, lean_object* v_cleanupAnnotations_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4936_; lean_object* v_res_4937_; 
v_cleanupAnnotations_boxed_4936_ = lean_unbox(v_cleanupAnnotations_4930_);
v_res_4937_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4926_, v_e_4927_, v_maxFVars_4928_, v_k_4929_, v_cleanupAnnotations_boxed_4936_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
lean_dec(v___y_4934_);
lean_dec_ref(v___y_4933_);
lean_dec(v___y_4932_);
lean_dec_ref(v___y_4931_);
return v_res_4937_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4938_){
_start:
{
if (lean_obj_tag(v_x_4938_) == 0)
{
uint8_t v___x_4939_; 
v___x_4939_ = 1;
return v___x_4939_;
}
else
{
lean_object* v_head_4940_; 
v_head_4940_ = lean_ctor_get(v_x_4938_, 0);
if (lean_obj_tag(v_head_4940_) == 0)
{
lean_object* v_tail_4941_; 
v_tail_4941_ = lean_ctor_get(v_x_4938_, 1);
v_x_4938_ = v_tail_4941_;
goto _start;
}
else
{
uint8_t v___x_4943_; 
v___x_4943_ = 0;
return v___x_4943_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4944_){
_start:
{
uint8_t v_res_4945_; lean_object* v_r_4946_; 
v_res_4945_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4944_);
lean_dec(v_x_4944_);
v_r_4946_ = lean_box(v_res_4945_);
return v_r_4946_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4949_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4950_ = lean_unsigned_to_nat(12u);
v___x_4951_ = lean_unsigned_to_nat(376u);
v___x_4952_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4953_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4954_ = l_mkPanicMessageWithDecl(v___x_4953_, v___x_4952_, v___x_4951_, v___x_4950_, v___x_4949_);
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4955_, lean_object* v_xs_4956_, lean_object* v_tail_4957_, lean_object* v___x_4958_, lean_object* v___x_4959_, lean_object* v_ys_4960_, lean_object* v_value_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
uint8_t v___x_1310__boxed_4967_; uint8_t v___x_1311__boxed_4968_; lean_object* v_res_4969_; 
v___x_1310__boxed_4967_ = lean_unbox(v___x_4958_);
v___x_1311__boxed_4968_ = lean_unbox(v___x_4959_);
v_res_4969_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4955_, v_xs_4956_, v_tail_4957_, v___x_1310__boxed_4967_, v___x_1311__boxed_4968_, v_ys_4960_, v_value_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec_ref(v_ys_4960_);
lean_dec(v___x_4955_);
return v_res_4969_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4970_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4971_ = lean_unsigned_to_nat(8u);
v___x_4972_ = lean_unsigned_to_nat(368u);
v___x_4973_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4974_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4975_ = l_mkPanicMessageWithDecl(v___x_4974_, v___x_4973_, v___x_4972_, v___x_4971_, v___x_4970_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4976_, lean_object* v_x_4977_, lean_object* v_x_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_){
_start:
{
if (lean_obj_tag(v_x_4977_) == 0)
{
lean_object* v___x_4984_; 
lean_dec_ref(v_xs_4976_);
v___x_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4984_, 0, v_x_4978_);
return v___x_4984_;
}
else
{
lean_object* v_head_4985_; 
v_head_4985_ = lean_ctor_get(v_x_4977_, 0);
if (lean_obj_tag(v_head_4985_) == 0)
{
lean_object* v_tail_4986_; uint8_t v___x_4987_; 
v_tail_4986_ = lean_ctor_get(v_x_4977_, 1);
lean_inc(v_tail_4986_);
lean_dec_ref_known(v_x_4977_, 2);
v___x_4987_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_4986_);
if (v___x_4987_ == 0)
{
uint8_t v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___f_4992_; lean_object* v___x_4993_; 
v___x_4988_ = 1;
v___x_4989_ = lean_unsigned_to_nat(1u);
v___x_4990_ = lean_box(v___x_4987_);
v___x_4991_ = lean_box(v___x_4988_);
v___f_4992_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4992_, 0, v___x_4989_);
lean_closure_set(v___f_4992_, 1, v_xs_4976_);
lean_closure_set(v___f_4992_, 2, v_tail_4986_);
lean_closure_set(v___f_4992_, 3, v___x_4990_);
lean_closure_set(v___f_4992_, 4, v___x_4991_);
v___x_4993_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_4978_, v___x_4989_, v___f_4992_, v___x_4987_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_);
return v___x_4993_;
}
else
{
lean_object* v___x_4994_; 
lean_dec(v_tail_4986_);
lean_dec_ref(v_xs_4976_);
v___x_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4994_, 0, v_x_4978_);
return v___x_4994_;
}
}
else
{
lean_object* v_tail_4995_; lean_object* v_val_4996_; lean_object* v___x_4997_; uint8_t v___x_4998_; 
lean_inc_ref(v_head_4985_);
v_tail_4995_ = lean_ctor_get(v_x_4977_, 1);
lean_inc(v_tail_4995_);
lean_dec_ref_known(v_x_4977_, 2);
v_val_4996_ = lean_ctor_get(v_head_4985_, 0);
lean_inc(v_val_4996_);
lean_dec_ref_known(v_head_4985_, 1);
v___x_4997_ = lean_array_get_size(v_xs_4976_);
v___x_4998_ = lean_nat_dec_lt(v_val_4996_, v___x_4997_);
if (v___x_4998_ == 0)
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
lean_dec(v_val_4996_);
lean_dec(v_tail_4995_);
lean_dec_ref(v_x_4978_);
lean_dec_ref(v_xs_4976_);
v___x_4999_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_5000_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4999_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_);
return v___x_5000_;
}
else
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5001_ = l_Lean_instInhabitedExpr;
v___x_5002_ = lean_array_get_borrowed(v___x_5001_, v_xs_4976_, v_val_4996_);
lean_dec(v_val_4996_);
v___x_5003_ = lean_unsigned_to_nat(1u);
v___x_5004_ = lean_mk_empty_array_with_capacity(v___x_5003_);
lean_inc(v___x_5002_);
v___x_5005_ = lean_array_push(v___x_5004_, v___x_5002_);
v___x_5006_ = l_Lean_Meta_instantiateLambda(v_x_4978_, v___x_5005_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_);
lean_dec_ref(v___x_5005_);
if (lean_obj_tag(v___x_5006_) == 0)
{
lean_object* v_a_5007_; 
v_a_5007_ = lean_ctor_get(v___x_5006_, 0);
lean_inc(v_a_5007_);
lean_dec_ref_known(v___x_5006_, 1);
v_x_4977_ = v_tail_4995_;
v_x_4978_ = v_a_5007_;
goto _start;
}
else
{
lean_dec(v_tail_4995_);
lean_dec_ref(v_xs_4976_);
return v___x_5006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_5009_, lean_object* v_xs_5010_, lean_object* v_tail_5011_, uint8_t v___x_5012_, uint8_t v___x_5013_, lean_object* v_ys_5014_, lean_object* v_value_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_){
_start:
{
lean_object* v___x_5021_; uint8_t v___x_5022_; 
v___x_5021_ = lean_array_get_size(v_ys_5014_);
v___x_5022_ = lean_nat_dec_eq(v___x_5021_, v___x_5009_);
if (v___x_5022_ == 0)
{
lean_object* v___x_5023_; lean_object* v___x_5024_; 
lean_dec_ref(v_value_5015_);
lean_dec(v_tail_5011_);
lean_dec_ref(v_xs_5010_);
v___x_5023_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_5024_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5023_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
return v___x_5024_;
}
else
{
lean_object* v___x_5025_; 
v___x_5025_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5010_, v_tail_5011_, v_value_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
if (lean_obj_tag(v___x_5025_) == 0)
{
lean_object* v_a_5026_; uint8_t v___x_5027_; lean_object* v___x_5028_; 
v_a_5026_ = lean_ctor_get(v___x_5025_, 0);
lean_inc(v_a_5026_);
lean_dec_ref_known(v___x_5025_, 1);
v___x_5027_ = 1;
v___x_5028_ = l_Lean_Meta_mkLambdaFVars(v_ys_5014_, v_a_5026_, v___x_5012_, v___x_5013_, v___x_5012_, v___x_5013_, v___x_5027_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
return v___x_5028_;
}
else
{
return v___x_5025_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_5029_, lean_object* v_x_5030_, lean_object* v_x_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5029_, v_x_5030_, v_x_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_);
lean_dec(v_a_5035_);
lean_dec_ref(v_a_5034_);
lean_dec(v_a_5033_);
lean_dec_ref(v_a_5032_);
return v_res_5037_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5039_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_5040_ = lean_unsigned_to_nat(2u);
v___x_5041_ = lean_unsigned_to_nat(362u);
v___x_5042_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_5043_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5044_ = l_mkPanicMessageWithDecl(v___x_5043_, v___x_5042_, v___x_5041_, v___x_5040_, v___x_5039_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_5045_, lean_object* v_value_u2080_5046_, lean_object* v_xs_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_){
_start:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; uint8_t v___x_5055_; 
v___x_5053_ = lean_array_get_size(v_xs_5047_);
v___x_5054_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5045_);
v___x_5055_ = lean_nat_dec_eq(v___x_5053_, v___x_5054_);
lean_dec(v___x_5054_);
if (v___x_5055_ == 0)
{
lean_object* v___x_5056_; lean_object* v___x_5057_; 
lean_dec_ref(v_xs_5047_);
lean_dec_ref(v_value_u2080_5046_);
lean_dec_ref(v_perm_5045_);
v___x_5056_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_5057_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5056_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_);
return v___x_5057_;
}
else
{
lean_object* v_mask_5058_; lean_object* v___x_5059_; 
v_mask_5058_ = lean_array_to_list(v_perm_5045_);
v___x_5059_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5047_, v_mask_5058_, v_value_u2080_5046_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_);
return v___x_5059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_5060_, lean_object* v_value_u2080_5061_, lean_object* v_xs_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_5060_, v_value_u2080_5061_, v_xs_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
lean_dec(v_a_5064_);
lean_dec_ref(v_a_5063_);
return v_res_5068_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_5076_; 
v___x_5076_ = l_Array_instInhabited(lean_box(0));
return v___x_5076_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5077_){
_start:
{
lean_object* v___f_5078_; lean_object* v___f_5079_; lean_object* v___f_5080_; lean_object* v___f_5081_; lean_object* v___f_5082_; lean_object* v___f_5083_; lean_object* v___f_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; 
v___f_5078_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5079_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5080_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5081_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5082_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5083_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5084_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5085_, 0, v___f_5078_);
lean_ctor_set(v___x_5085_, 1, v___f_5079_);
v___x_5086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5086_, 0, v___x_5085_);
lean_ctor_set(v___x_5086_, 1, v___f_5080_);
lean_ctor_set(v___x_5086_, 2, v___f_5081_);
lean_ctor_set(v___x_5086_, 3, v___f_5082_);
lean_ctor_set(v___x_5086_, 4, v___f_5083_);
v___x_5087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5087_, 0, v___x_5086_);
lean_ctor_set(v___x_5087_, 1, v___f_5084_);
v___x_5088_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5089_ = l_instInhabitedOfMonad___redArg(v___x_5087_, v___x_5088_);
v___x_5090_ = lean_panic_fn_borrowed(v___x_5089_, v_msg_5077_);
lean_dec(v___x_5089_);
return v___x_5090_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5091_, lean_object* v_msg_5092_){
_start:
{
lean_object* v___x_5093_; 
v___x_5093_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5092_);
return v___x_5093_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; 
v___x_5096_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5097_ = lean_unsigned_to_nat(8u);
v___x_5098_ = lean_unsigned_to_nat(394u);
v___x_5099_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5100_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5101_ = l_mkPanicMessageWithDecl(v___x_5100_, v___x_5099_, v___x_5098_, v___x_5097_, v___x_5096_);
return v___x_5101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5102_, lean_object* v_x_5103_){
_start:
{
if (lean_obj_tag(v_x_5102_) == 0)
{
return v_x_5103_;
}
else
{
lean_object* v_head_5104_; lean_object* v_fst_5105_; 
v_head_5104_ = lean_ctor_get(v_x_5102_, 0);
v_fst_5105_ = lean_ctor_get(v_head_5104_, 0);
if (lean_obj_tag(v_fst_5105_) == 0)
{
lean_object* v_tail_5106_; 
v_tail_5106_ = lean_ctor_get(v_x_5102_, 1);
lean_inc(v_tail_5106_);
lean_dec_ref_known(v_x_5102_, 2);
v_x_5102_ = v_tail_5106_;
goto _start;
}
else
{
lean_object* v_tail_5108_; lean_object* v_snd_5109_; lean_object* v_val_5110_; lean_object* v___x_5111_; uint8_t v___x_5112_; 
lean_inc_ref(v_fst_5105_);
lean_inc(v_head_5104_);
v_tail_5108_ = lean_ctor_get(v_x_5102_, 1);
lean_inc(v_tail_5108_);
lean_dec_ref_known(v_x_5102_, 2);
v_snd_5109_ = lean_ctor_get(v_head_5104_, 1);
lean_inc(v_snd_5109_);
lean_dec(v_head_5104_);
v_val_5110_ = lean_ctor_get(v_fst_5105_, 0);
lean_inc(v_val_5110_);
lean_dec_ref_known(v_fst_5105_, 1);
v___x_5111_ = lean_array_get_size(v_x_5103_);
v___x_5112_ = lean_nat_dec_lt(v_val_5110_, v___x_5111_);
if (v___x_5112_ == 0)
{
lean_object* v___x_5113_; lean_object* v___x_5114_; 
lean_dec(v_val_5110_);
lean_dec(v_snd_5109_);
lean_dec(v_tail_5108_);
lean_dec_ref(v_x_5103_);
v___x_5113_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5114_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5113_);
return v___x_5114_;
}
else
{
lean_object* v___x_5115_; 
v___x_5115_ = lean_array_set(v_x_5103_, v_val_5110_, v_snd_5109_);
lean_dec(v_val_5110_);
v_x_5102_ = v_tail_5108_;
v_x_5103_ = v___x_5115_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5117_, lean_object* v_x_5118_, lean_object* v_x_5119_){
_start:
{
lean_object* v___x_5120_; 
v___x_5120_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5118_, v_x_5119_);
return v___x_5120_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v___x_5123_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5124_ = lean_unsigned_to_nat(2u);
v___x_5125_ = lean_unsigned_to_nat(384u);
v___x_5126_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5127_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5128_ = l_mkPanicMessageWithDecl(v___x_5127_, v___x_5126_, v___x_5125_, v___x_5124_, v___x_5123_);
return v___x_5128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5131_, lean_object* v_xs_5132_){
_start:
{
lean_object* v___x_5133_; lean_object* v___x_5134_; uint8_t v___x_5135_; 
v___x_5133_ = lean_array_get_size(v_xs_5132_);
v___x_5134_ = lean_array_get_size(v_perm_5131_);
v___x_5135_ = lean_nat_dec_eq(v___x_5133_, v___x_5134_);
if (v___x_5135_ == 0)
{
lean_object* v___x_5136_; lean_object* v___x_5137_; 
v___x_5136_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5137_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5136_);
return v___x_5137_;
}
else
{
lean_object* v___x_5138_; uint8_t v___x_5139_; 
v___x_5138_ = lean_unsigned_to_nat(0u);
v___x_5139_ = lean_nat_dec_eq(v___x_5133_, v___x_5138_);
if (v___x_5139_ == 0)
{
lean_object* v_dummy_5140_; lean_object* v___x_5141_; lean_object* v_ys_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; 
v_dummy_5140_ = lean_array_fget_borrowed(v_xs_5132_, v___x_5138_);
v___x_5141_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5131_);
lean_inc(v_dummy_5140_);
v_ys_5142_ = lean_mk_array(v___x_5141_, v_dummy_5140_);
v___x_5143_ = l_Array_zip___redArg(v_perm_5131_, v_xs_5132_);
v___x_5144_ = lean_array_to_list(v___x_5143_);
v___x_5145_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5144_, v_ys_5142_);
return v___x_5145_;
}
else
{
lean_object* v___x_5146_; 
v___x_5146_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5147_, lean_object* v_xs_5148_){
_start:
{
lean_object* v_res_5149_; 
v_res_5149_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5147_, v_xs_5148_);
lean_dec_ref(v_xs_5148_);
lean_dec_ref(v_perm_5147_);
return v_res_5149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5150_, lean_object* v_perm_5151_, lean_object* v_xs_5152_){
_start:
{
lean_object* v___x_5153_; 
v___x_5153_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5151_, v_xs_5152_);
return v___x_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5154_, lean_object* v_perm_5155_, lean_object* v_xs_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5154_, v_perm_5155_, v_xs_5156_);
lean_dec_ref(v_xs_5156_);
lean_dec_ref(v_perm_5155_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5158_, lean_object* v_upperBound_5159_, lean_object* v_perm_5160_, lean_object* v_a_5161_, lean_object* v_b_5162_){
_start:
{
lean_object* v_a_5164_; uint8_t v___x_5171_; 
v___x_5171_ = lean_nat_dec_lt(v_a_5161_, v_upperBound_5159_);
if (v___x_5171_ == 0)
{
lean_dec(v_a_5161_);
return v_b_5162_;
}
else
{
lean_object* v___x_5172_; uint8_t v___x_5173_; 
v___x_5172_ = lean_array_get_size(v_perm_5160_);
v___x_5173_ = lean_nat_dec_lt(v_a_5161_, v___x_5172_);
if (v___x_5173_ == 0)
{
goto v___jp_5168_;
}
else
{
lean_object* v___x_5174_; 
v___x_5174_ = lean_array_fget_borrowed(v_perm_5160_, v_a_5161_);
if (lean_obj_tag(v___x_5174_) == 0)
{
goto v___jp_5168_;
}
else
{
v_a_5164_ = v_b_5162_;
goto v___jp_5163_;
}
}
}
v___jp_5163_:
{
lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_5165_ = lean_unsigned_to_nat(1u);
v___x_5166_ = lean_nat_add(v_a_5161_, v___x_5165_);
lean_dec(v_a_5161_);
v_a_5161_ = v___x_5166_;
v_b_5162_ = v_a_5164_;
goto _start;
}
v___jp_5168_:
{
lean_object* v___x_5169_; lean_object* v___x_5170_; 
v___x_5169_ = lean_array_fget_borrowed(v_xs_5158_, v_a_5161_);
lean_inc(v___x_5169_);
v___x_5170_ = lean_array_push(v_b_5162_, v___x_5169_);
v_a_5164_ = v___x_5170_;
goto v___jp_5163_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5175_, lean_object* v_upperBound_5176_, lean_object* v_perm_5177_, lean_object* v_a_5178_, lean_object* v_b_5179_){
_start:
{
lean_object* v_res_5180_; 
v_res_5180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5175_, v_upperBound_5176_, v_perm_5177_, v_a_5178_, v_b_5179_);
lean_dec_ref(v_perm_5177_);
lean_dec(v_upperBound_5176_);
lean_dec_ref(v_xs_5175_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5181_, lean_object* v_xs_5182_){
_start:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v_ys_5185_; lean_object* v___x_5186_; 
v___x_5183_ = lean_array_get_size(v_xs_5182_);
v___x_5184_ = lean_unsigned_to_nat(0u);
v_ys_5185_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5186_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5182_, v___x_5183_, v_perm_5181_, v___x_5184_, v_ys_5185_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5187_, lean_object* v_xs_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5187_, v_xs_5188_);
lean_dec_ref(v_xs_5188_);
lean_dec_ref(v_perm_5187_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5190_, lean_object* v_perm_5191_, lean_object* v_xs_5192_){
_start:
{
lean_object* v___x_5193_; 
v___x_5193_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5191_, v_xs_5192_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5194_, lean_object* v_perm_5195_, lean_object* v_xs_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5194_, v_perm_5195_, v_xs_5196_);
lean_dec_ref(v_xs_5196_);
lean_dec_ref(v_perm_5195_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5198_, lean_object* v_xs_5199_, lean_object* v_upperBound_5200_, lean_object* v_perm_5201_, lean_object* v_inst_5202_, lean_object* v_R_5203_, lean_object* v_a_5204_, lean_object* v_b_5205_, lean_object* v_c_5206_){
_start:
{
lean_object* v___x_5207_; 
v___x_5207_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5199_, v_upperBound_5200_, v_perm_5201_, v_a_5204_, v_b_5205_);
return v___x_5207_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5208_, lean_object* v_xs_5209_, lean_object* v_upperBound_5210_, lean_object* v_perm_5211_, lean_object* v_inst_5212_, lean_object* v_R_5213_, lean_object* v_a_5214_, lean_object* v_b_5215_, lean_object* v_c_5216_){
_start:
{
lean_object* v_res_5217_; 
v_res_5217_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5208_, v_xs_5209_, v_upperBound_5210_, v_perm_5211_, v_inst_5212_, v_R_5213_, v_a_5214_, v_b_5215_, v_c_5216_);
lean_dec_ref(v_perm_5211_);
lean_dec(v_upperBound_5210_);
lean_dec_ref(v_xs_5209_);
return v_res_5217_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(lean_object* v_msg_5218_){
_start:
{
lean_object* v___x_5219_; lean_object* v___x_5220_; 
v___x_5219_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5220_ = lean_panic_fn_borrowed(v___x_5219_, v_msg_5218_);
return v___x_5220_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_00_u03b1_5221_, lean_object* v_msg_5222_){
_start:
{
lean_object* v___x_5223_; 
v___x_5223_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v_msg_5222_);
return v___x_5223_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_as_5224_, size_t v_i_5225_, size_t v_stop_5226_){
_start:
{
uint8_t v___x_5227_; 
v___x_5227_ = lean_usize_dec_eq(v_i_5225_, v_stop_5226_);
if (v___x_5227_ == 0)
{
uint8_t v___x_5228_; lean_object* v___x_5229_; 
v___x_5228_ = 1;
v___x_5229_ = lean_array_uget_borrowed(v_as_5224_, v_i_5225_);
if (lean_obj_tag(v___x_5229_) == 0)
{
if (v___x_5227_ == 0)
{
size_t v___x_5230_; size_t v___x_5231_; 
v___x_5230_ = ((size_t)1ULL);
v___x_5231_ = lean_usize_add(v_i_5225_, v___x_5230_);
v_i_5225_ = v___x_5231_;
goto _start;
}
else
{
return v___x_5228_;
}
}
else
{
return v___x_5228_;
}
}
else
{
uint8_t v___x_5233_; 
v___x_5233_ = 0;
return v___x_5233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___boxed(lean_object* v_as_5234_, lean_object* v_i_5235_, lean_object* v_stop_5236_){
_start:
{
size_t v_i_boxed_5237_; size_t v_stop_boxed_5238_; uint8_t v_res_5239_; lean_object* v_r_5240_; 
v_i_boxed_5237_ = lean_unbox_usize(v_i_5235_);
lean_dec(v_i_5235_);
v_stop_boxed_5238_ = lean_unbox_usize(v_stop_5236_);
lean_dec(v_stop_5236_);
v_res_5239_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v_as_5234_, v_i_boxed_5237_, v_stop_boxed_5238_);
lean_dec_ref(v_as_5234_);
v_r_5240_ = lean_box(v_res_5239_);
return v_r_5240_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; 
v___x_5243_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5244_ = lean_unsigned_to_nat(12u);
v___x_5245_ = lean_unsigned_to_nat(433u);
v___x_5246_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5247_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5248_ = l_mkPanicMessageWithDecl(v___x_5247_, v___x_5246_, v___x_5245_, v___x_5244_, v___x_5243_);
return v___x_5248_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
v___x_5250_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5251_ = lean_unsigned_to_nat(10u);
v___x_5252_ = lean_unsigned_to_nat(425u);
v___x_5253_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5254_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5255_ = l_mkPanicMessageWithDecl(v___x_5254_, v___x_5253_, v___x_5252_, v___x_5251_, v___x_5250_);
return v___x_5255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5256_, lean_object* v_fixedArgs_5257_, lean_object* v_varyingArgs_5258_, lean_object* v_i_5259_, lean_object* v_j_5260_, lean_object* v_xs_5261_){
_start:
{
lean_object* v_lower_5263_; lean_object* v_upper_5264_; lean_object* v___y_5269_; lean_object* v___y_5270_; lean_object* v___y_5271_; lean_object* v_lower_5279_; lean_object* v_upper_5280_; lean_object* v___x_5288_; uint8_t v___x_5289_; 
v___x_5288_ = lean_array_get_size(v_perm_5256_);
v___x_5289_ = lean_nat_dec_lt(v_i_5259_, v___x_5288_);
if (v___x_5289_ == 0)
{
lean_object* v___x_5290_; lean_object* v___x_5291_; uint8_t v___x_5292_; 
lean_dec(v_i_5259_);
lean_dec_ref(v_perm_5256_);
v___x_5290_ = lean_unsigned_to_nat(0u);
v___x_5291_ = lean_array_get_size(v_varyingArgs_5258_);
v___x_5292_ = lean_nat_dec_le(v_j_5260_, v___x_5290_);
if (v___x_5292_ == 0)
{
v_lower_5263_ = v_j_5260_;
v_upper_5264_ = v___x_5291_;
goto v___jp_5262_;
}
else
{
lean_dec(v_j_5260_);
v_lower_5263_ = v___x_5290_;
v_upper_5264_ = v___x_5291_;
goto v___jp_5262_;
}
}
else
{
lean_object* v___x_5293_; 
v___x_5293_ = lean_array_fget_borrowed(v_perm_5256_, v_i_5259_);
if (lean_obj_tag(v___x_5293_) == 1)
{
lean_object* v_val_5294_; lean_object* v___x_5295_; uint8_t v___x_5296_; 
v_val_5294_ = lean_ctor_get(v___x_5293_, 0);
v___x_5295_ = lean_array_get_size(v_fixedArgs_5257_);
v___x_5296_ = lean_nat_dec_lt(v_val_5294_, v___x_5295_);
if (v___x_5296_ == 0)
{
lean_object* v___x_5297_; lean_object* v___x_5298_; 
lean_dec_ref(v_xs_5261_);
lean_dec(v_j_5260_);
lean_dec(v_i_5259_);
lean_dec_ref(v_varyingArgs_5258_);
lean_dec_ref(v_perm_5256_);
v___x_5297_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5298_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5297_);
return v___x_5298_;
}
else
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; 
v___x_5299_ = lean_unsigned_to_nat(1u);
v___x_5300_ = lean_nat_add(v_i_5259_, v___x_5299_);
lean_dec(v_i_5259_);
v___x_5301_ = lean_array_fget_borrowed(v_fixedArgs_5257_, v_val_5294_);
lean_inc(v___x_5301_);
v___x_5302_ = lean_array_push(v_xs_5261_, v___x_5301_);
v_i_5259_ = v___x_5300_;
v_xs_5261_ = v___x_5302_;
goto _start;
}
}
else
{
lean_object* v___x_5304_; uint8_t v___x_5305_; 
v___x_5304_ = lean_array_get_size(v_varyingArgs_5258_);
v___x_5305_ = lean_nat_dec_lt(v_j_5260_, v___x_5304_);
if (v___x_5305_ == 0)
{
lean_object* v___x_5306_; uint8_t v___x_5307_; 
lean_dec(v_j_5260_);
lean_dec_ref(v_varyingArgs_5258_);
v___x_5306_ = lean_unsigned_to_nat(0u);
v___x_5307_ = lean_nat_dec_le(v_i_5259_, v___x_5306_);
if (v___x_5307_ == 0)
{
v_lower_5279_ = v_i_5259_;
v_upper_5280_ = v___x_5288_;
goto v___jp_5278_;
}
else
{
lean_dec(v_i_5259_);
v_lower_5279_ = v___x_5306_;
v_upper_5280_ = v___x_5288_;
goto v___jp_5278_;
}
}
else
{
lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; 
v___x_5308_ = lean_unsigned_to_nat(1u);
v___x_5309_ = lean_nat_add(v_i_5259_, v___x_5308_);
lean_dec(v_i_5259_);
v___x_5310_ = lean_nat_add(v_j_5260_, v___x_5308_);
v___x_5311_ = lean_array_fget_borrowed(v_varyingArgs_5258_, v_j_5260_);
lean_dec(v_j_5260_);
lean_inc(v___x_5311_);
v___x_5312_ = lean_array_push(v_xs_5261_, v___x_5311_);
v_i_5259_ = v___x_5309_;
v_j_5260_ = v___x_5310_;
v_xs_5261_ = v___x_5312_;
goto _start;
}
}
}
v___jp_5262_:
{
lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; 
v___x_5265_ = l_Array_toSubarray___redArg(v_varyingArgs_5258_, v_lower_5263_, v_upper_5264_);
v___x_5266_ = l_Subarray_copy___redArg(v___x_5265_);
v___x_5267_ = l_Array_append___redArg(v_xs_5261_, v___x_5266_);
lean_dec_ref(v___x_5266_);
return v___x_5267_;
}
v___jp_5268_:
{
uint8_t v___x_5272_; 
v___x_5272_ = lean_nat_dec_lt(v___y_5269_, v___y_5271_);
if (v___x_5272_ == 0)
{
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
lean_dec(v___y_5269_);
return v_xs_5261_;
}
else
{
size_t v___x_5273_; size_t v___x_5274_; uint8_t v___x_5275_; 
v___x_5273_ = lean_usize_of_nat(v___y_5269_);
lean_dec(v___y_5269_);
v___x_5274_ = lean_usize_of_nat(v___y_5271_);
lean_dec(v___y_5271_);
v___x_5275_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v___y_5270_, v___x_5273_, v___x_5274_);
lean_dec_ref(v___y_5270_);
if (v___x_5275_ == 0)
{
return v_xs_5261_;
}
else
{
lean_object* v___x_5276_; lean_object* v___x_5277_; 
lean_dec_ref(v_xs_5261_);
v___x_5276_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5277_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5276_);
return v___x_5277_;
}
}
}
v___jp_5278_:
{
lean_object* v___x_5281_; lean_object* v_array_5282_; lean_object* v_start_5283_; lean_object* v_stop_5284_; uint8_t v___x_5285_; 
v___x_5281_ = l_Array_toSubarray___redArg(v_perm_5256_, v_lower_5279_, v_upper_5280_);
v_array_5282_ = lean_ctor_get(v___x_5281_, 0);
lean_inc_ref(v_array_5282_);
v_start_5283_ = lean_ctor_get(v___x_5281_, 1);
lean_inc(v_start_5283_);
v_stop_5284_ = lean_ctor_get(v___x_5281_, 2);
lean_inc(v_stop_5284_);
lean_dec_ref(v___x_5281_);
v___x_5285_ = lean_nat_dec_lt(v_start_5283_, v_stop_5284_);
if (v___x_5285_ == 0)
{
lean_dec(v_stop_5284_);
lean_dec(v_start_5283_);
lean_dec_ref(v_array_5282_);
return v_xs_5261_;
}
else
{
lean_object* v___x_5286_; uint8_t v___x_5287_; 
v___x_5286_ = lean_array_get_size(v_array_5282_);
v___x_5287_ = lean_nat_dec_le(v_stop_5284_, v___x_5286_);
if (v___x_5287_ == 0)
{
lean_dec(v_stop_5284_);
v___y_5269_ = v_start_5283_;
v___y_5270_ = v_array_5282_;
v___y_5271_ = v___x_5286_;
goto v___jp_5268_;
}
else
{
v___y_5269_ = v_start_5283_;
v___y_5270_ = v_array_5282_;
v___y_5271_ = v_stop_5284_;
goto v___jp_5268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5314_, lean_object* v_fixedArgs_5315_, lean_object* v_varyingArgs_5316_, lean_object* v_i_5317_, lean_object* v_j_5318_, lean_object* v_xs_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5314_, v_fixedArgs_5315_, v_varyingArgs_5316_, v_i_5317_, v_j_5318_, v_xs_5319_);
lean_dec_ref(v_fixedArgs_5315_);
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5321_, lean_object* v_perm_5322_, lean_object* v_fixedArgs_5323_, lean_object* v_varyingArgs_5324_, lean_object* v_i_5325_, lean_object* v_j_5326_, lean_object* v_xs_5327_){
_start:
{
lean_object* v___x_5328_; 
v___x_5328_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5322_, v_fixedArgs_5323_, v_varyingArgs_5324_, v_i_5325_, v_j_5326_, v_xs_5327_);
return v___x_5328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5329_, lean_object* v_perm_5330_, lean_object* v_fixedArgs_5331_, lean_object* v_varyingArgs_5332_, lean_object* v_i_5333_, lean_object* v_j_5334_, lean_object* v_xs_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5329_, v_perm_5330_, v_fixedArgs_5331_, v_varyingArgs_5332_, v_i_5333_, v_j_5334_, v_xs_5335_);
lean_dec_ref(v_fixedArgs_5331_);
return v_res_5336_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; 
v___x_5339_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5340_ = lean_unsigned_to_nat(2u);
v___x_5341_ = lean_unsigned_to_nat(416u);
v___x_5342_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5343_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5344_ = l_mkPanicMessageWithDecl(v___x_5343_, v___x_5342_, v___x_5341_, v___x_5340_, v___x_5339_);
return v___x_5344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5345_, lean_object* v_fixedArgs_5346_, lean_object* v_varyingArgs_5347_){
_start:
{
lean_object* v___x_5348_; lean_object* v___x_5349_; uint8_t v___x_5350_; 
v___x_5348_ = lean_array_get_size(v_fixedArgs_5346_);
v___x_5349_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5345_);
v___x_5350_ = lean_nat_dec_eq(v___x_5348_, v___x_5349_);
lean_dec(v___x_5349_);
if (v___x_5350_ == 0)
{
lean_object* v___x_5351_; lean_object* v___x_5352_; 
lean_dec_ref(v_varyingArgs_5347_);
lean_dec_ref(v_perm_5345_);
v___x_5351_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5352_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5351_);
return v___x_5352_;
}
else
{
lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; 
v___x_5353_ = lean_unsigned_to_nat(0u);
v___x_5354_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5355_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5345_, v_fixedArgs_5346_, v_varyingArgs_5347_, v___x_5353_, v___x_5353_, v___x_5354_);
return v___x_5355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5356_, lean_object* v_fixedArgs_5357_, lean_object* v_varyingArgs_5358_){
_start:
{
lean_object* v_res_5359_; 
v_res_5359_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5356_, v_fixedArgs_5357_, v_varyingArgs_5358_);
lean_dec_ref(v_fixedArgs_5357_);
return v_res_5359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5360_, lean_object* v_perm_5361_, lean_object* v_fixedArgs_5362_, lean_object* v_varyingArgs_5363_){
_start:
{
lean_object* v___x_5364_; 
v___x_5364_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5361_, v_fixedArgs_5362_, v_varyingArgs_5363_);
return v___x_5364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5365_, lean_object* v_perm_5366_, lean_object* v_fixedArgs_5367_, lean_object* v_varyingArgs_5368_){
_start:
{
lean_object* v_res_5369_; 
v_res_5369_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5365_, v_perm_5366_, v_fixedArgs_5367_, v_varyingArgs_5368_);
lean_dec_ref(v_fixedArgs_5367_);
return v_res_5369_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5370_, lean_object* v_x_5371_){
_start:
{
if (lean_obj_tag(v_x_5370_) == 0)
{
if (lean_obj_tag(v_x_5371_) == 0)
{
uint8_t v___x_5372_; 
v___x_5372_ = 1;
return v___x_5372_;
}
else
{
uint8_t v___x_5373_; 
v___x_5373_ = 0;
return v___x_5373_;
}
}
else
{
if (lean_obj_tag(v_x_5371_) == 0)
{
uint8_t v___x_5374_; 
v___x_5374_ = 0;
return v___x_5374_;
}
else
{
lean_object* v_val_5375_; lean_object* v_val_5376_; uint8_t v___x_5377_; 
v_val_5375_ = lean_ctor_get(v_x_5370_, 0);
v_val_5376_ = lean_ctor_get(v_x_5371_, 0);
v___x_5377_ = lean_nat_dec_eq(v_val_5375_, v_val_5376_);
return v___x_5377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5378_, lean_object* v_x_5379_){
_start:
{
uint8_t v_res_5380_; lean_object* v_r_5381_; 
v_res_5380_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5378_, v_x_5379_);
lean_dec(v_x_5379_);
lean_dec(v_x_5378_);
v_r_5381_ = lean_box(v_res_5380_);
return v_r_5381_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5382_, lean_object* v_ys_5383_, lean_object* v_x_5384_){
_start:
{
lean_object* v_zero_5385_; uint8_t v_isZero_5386_; 
v_zero_5385_ = lean_unsigned_to_nat(0u);
v_isZero_5386_ = lean_nat_dec_eq(v_x_5384_, v_zero_5385_);
if (v_isZero_5386_ == 1)
{
lean_dec(v_x_5384_);
return v_isZero_5386_;
}
else
{
lean_object* v_one_5387_; lean_object* v_n_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; uint8_t v___x_5391_; 
v_one_5387_ = lean_unsigned_to_nat(1u);
v_n_5388_ = lean_nat_sub(v_x_5384_, v_one_5387_);
lean_dec(v_x_5384_);
v___x_5389_ = lean_array_fget_borrowed(v_xs_5382_, v_n_5388_);
v___x_5390_ = lean_array_fget_borrowed(v_ys_5383_, v_n_5388_);
v___x_5391_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5389_, v___x_5390_);
if (v___x_5391_ == 0)
{
lean_dec(v_n_5388_);
return v___x_5391_;
}
else
{
v_x_5384_ = v_n_5388_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5393_, lean_object* v_ys_5394_, lean_object* v_x_5395_){
_start:
{
uint8_t v_res_5396_; lean_object* v_r_5397_; 
v_res_5396_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5393_, v_ys_5394_, v_x_5395_);
lean_dec_ref(v_ys_5394_);
lean_dec_ref(v_xs_5393_);
v_r_5397_ = lean_box(v_res_5396_);
return v_r_5397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5398_, size_t v_i_5399_, lean_object* v_bs_5400_){
_start:
{
uint8_t v___x_5401_; 
v___x_5401_ = lean_usize_dec_lt(v_i_5399_, v_sz_5398_);
if (v___x_5401_ == 0)
{
return v_bs_5400_;
}
else
{
lean_object* v_v_5402_; lean_object* v___x_5403_; lean_object* v_bs_x27_5404_; lean_object* v___x_5405_; size_t v___x_5406_; size_t v___x_5407_; lean_object* v___x_5408_; 
v_v_5402_ = lean_array_uget(v_bs_5400_, v_i_5399_);
v___x_5403_ = lean_unsigned_to_nat(0u);
v_bs_x27_5404_ = lean_array_uset(v_bs_5400_, v_i_5399_, v___x_5403_);
v___x_5405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5405_, 0, v_v_5402_);
v___x_5406_ = ((size_t)1ULL);
v___x_5407_ = lean_usize_add(v_i_5399_, v___x_5406_);
v___x_5408_ = lean_array_uset(v_bs_x27_5404_, v_i_5399_, v___x_5405_);
v_i_5399_ = v___x_5407_;
v_bs_5400_ = v___x_5408_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5410_, lean_object* v_i_5411_, lean_object* v_bs_5412_){
_start:
{
size_t v_sz_boxed_5413_; size_t v_i_boxed_5414_; lean_object* v_res_5415_; 
v_sz_boxed_5413_ = lean_unbox_usize(v_sz_5410_);
lean_dec(v_sz_5410_);
v_i_boxed_5414_ = lean_unbox_usize(v_i_5411_);
lean_dec(v_i_5411_);
v_res_5415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5413_, v_i_boxed_5414_, v_bs_5412_);
return v_res_5415_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5416_, lean_object* v_as_5417_, size_t v_i_5418_, size_t v_stop_5419_){
_start:
{
uint8_t v___x_5420_; 
v___x_5420_ = lean_usize_dec_eq(v_i_5418_, v_stop_5419_);
if (v___x_5420_ == 0)
{
lean_object* v_numFixed_5421_; uint8_t v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; size_t v_sz_5425_; size_t v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; uint8_t v___x_5434_; 
v_numFixed_5421_ = lean_ctor_get(v_fixedParamPerms_5416_, 0);
v___x_5422_ = 1;
v___x_5423_ = lean_array_uget_borrowed(v_as_5417_, v_i_5418_);
lean_inc(v_numFixed_5421_);
v___x_5424_ = l_Array_range(v_numFixed_5421_);
v_sz_5425_ = lean_array_size(v___x_5424_);
v___x_5426_ = ((size_t)0ULL);
v___x_5427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5425_, v___x_5426_, v___x_5424_);
v___x_5428_ = lean_array_get_size(v___x_5423_);
v___x_5429_ = lean_nat_sub(v___x_5428_, v_numFixed_5421_);
v___x_5430_ = lean_box(0);
v___x_5431_ = lean_mk_array(v___x_5429_, v___x_5430_);
v___x_5432_ = l_Array_append___redArg(v___x_5427_, v___x_5431_);
lean_dec_ref(v___x_5431_);
v___x_5433_ = lean_array_get_size(v___x_5432_);
v___x_5434_ = lean_nat_dec_eq(v___x_5428_, v___x_5433_);
if (v___x_5434_ == 0)
{
lean_dec_ref(v___x_5432_);
lean_dec_ref(v_fixedParamPerms_5416_);
return v___x_5422_;
}
else
{
uint8_t v___x_5435_; 
v___x_5435_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5423_, v___x_5432_, v___x_5428_);
lean_dec_ref(v___x_5432_);
if (v___x_5435_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5416_);
return v___x_5422_;
}
else
{
if (v___x_5420_ == 0)
{
size_t v___x_5436_; size_t v___x_5437_; 
v___x_5436_ = ((size_t)1ULL);
v___x_5437_ = lean_usize_add(v_i_5418_, v___x_5436_);
v_i_5418_ = v___x_5437_;
goto _start;
}
else
{
lean_dec_ref(v_fixedParamPerms_5416_);
return v___x_5422_;
}
}
}
}
else
{
uint8_t v___x_5439_; 
lean_dec_ref(v_fixedParamPerms_5416_);
v___x_5439_ = 0;
return v___x_5439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5440_, lean_object* v_as_5441_, lean_object* v_i_5442_, lean_object* v_stop_5443_){
_start:
{
size_t v_i_boxed_5444_; size_t v_stop_boxed_5445_; uint8_t v_res_5446_; lean_object* v_r_5447_; 
v_i_boxed_5444_ = lean_unbox_usize(v_i_5442_);
lean_dec(v_i_5442_);
v_stop_boxed_5445_ = lean_unbox_usize(v_stop_5443_);
lean_dec(v_stop_5443_);
v_res_5446_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5440_, v_as_5441_, v_i_boxed_5444_, v_stop_boxed_5445_);
lean_dec_ref(v_as_5441_);
v_r_5447_ = lean_box(v_res_5446_);
return v_r_5447_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5448_){
_start:
{
lean_object* v_perms_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; uint8_t v___x_5452_; 
v_perms_5449_ = lean_ctor_get(v_fixedParamPerms_5448_, 1);
lean_inc_ref(v_perms_5449_);
v___x_5450_ = lean_unsigned_to_nat(0u);
v___x_5451_ = lean_array_get_size(v_perms_5449_);
v___x_5452_ = lean_nat_dec_lt(v___x_5450_, v___x_5451_);
if (v___x_5452_ == 0)
{
uint8_t v___x_5453_; 
lean_dec_ref(v_perms_5449_);
lean_dec_ref(v_fixedParamPerms_5448_);
v___x_5453_ = 1;
return v___x_5453_;
}
else
{
if (v___x_5452_ == 0)
{
lean_dec_ref(v_perms_5449_);
lean_dec_ref(v_fixedParamPerms_5448_);
return v___x_5452_;
}
else
{
size_t v___x_5454_; size_t v___x_5455_; uint8_t v___x_5456_; 
v___x_5454_ = ((size_t)0ULL);
v___x_5455_ = lean_usize_of_nat(v___x_5451_);
v___x_5456_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5448_, v_perms_5449_, v___x_5454_, v___x_5455_);
lean_dec_ref(v_perms_5449_);
if (v___x_5456_ == 0)
{
return v___x_5452_;
}
else
{
uint8_t v___x_5457_; 
v___x_5457_ = 0;
return v___x_5457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5458_){
_start:
{
uint8_t v_res_5459_; lean_object* v_r_5460_; 
v_res_5459_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5458_);
v_r_5460_ = lean_box(v_res_5459_);
return v_r_5460_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5461_, lean_object* v_ys_5462_, lean_object* v_hsz_5463_, lean_object* v_x_5464_, lean_object* v_x_5465_){
_start:
{
uint8_t v___x_5466_; 
v___x_5466_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5461_, v_ys_5462_, v_x_5464_);
return v___x_5466_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5467_, lean_object* v_ys_5468_, lean_object* v_hsz_5469_, lean_object* v_x_5470_, lean_object* v_x_5471_){
_start:
{
uint8_t v_res_5472_; lean_object* v_r_5473_; 
v_res_5472_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5467_, v_ys_5468_, v_hsz_5469_, v_x_5470_, v_x_5471_);
lean_dec_ref(v_ys_5468_);
lean_dec_ref(v_xs_5467_);
v_r_5473_ = lean_box(v_res_5472_);
return v_r_5473_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5474_; 
v___x_5474_ = l_Array_instInhabited(lean_box(0));
return v___x_5474_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5475_){
_start:
{
lean_object* v___f_5476_; lean_object* v___f_5477_; lean_object* v___f_5478_; lean_object* v___f_5479_; lean_object* v___f_5480_; lean_object* v___f_5481_; lean_object* v___f_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; 
v___f_5476_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5477_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5478_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5479_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5480_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5481_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5482_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5483_, 0, v___f_5476_);
lean_ctor_set(v___x_5483_, 1, v___f_5477_);
v___x_5484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5484_, 0, v___x_5483_);
lean_ctor_set(v___x_5484_, 1, v___f_5478_);
lean_ctor_set(v___x_5484_, 2, v___f_5479_);
lean_ctor_set(v___x_5484_, 3, v___f_5480_);
lean_ctor_set(v___x_5484_, 4, v___f_5481_);
v___x_5485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5485_, 0, v___x_5484_);
lean_ctor_set(v___x_5485_, 1, v___f_5482_);
v___x_5486_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5487_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5488_, 0, v___x_5487_);
lean_ctor_set(v___x_5488_, 1, v___x_5487_);
v___x_5489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5489_, 0, v___x_5486_);
lean_ctor_set(v___x_5489_, 1, v___x_5488_);
v___x_5490_ = l_instInhabitedOfMonad___redArg(v___x_5485_, v___x_5489_);
v___x_5491_ = lean_panic_fn_borrowed(v___x_5490_, v_msg_5475_);
lean_dec(v___x_5490_);
return v___x_5491_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5492_; 
v___x_5492_ = l_Array_instInhabited(lean_box(0));
return v___x_5492_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5493_){
_start:
{
lean_object* v___f_5494_; lean_object* v___f_5495_; lean_object* v___f_5496_; lean_object* v___f_5497_; lean_object* v___f_5498_; lean_object* v___f_5499_; lean_object* v___f_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; 
v___f_5494_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5495_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5496_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5497_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5498_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5499_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5500_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5501_, 0, v___f_5494_);
lean_ctor_set(v___x_5501_, 1, v___f_5495_);
v___x_5502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5502_, 0, v___x_5501_);
lean_ctor_set(v___x_5502_, 1, v___f_5496_);
lean_ctor_set(v___x_5502_, 2, v___f_5497_);
lean_ctor_set(v___x_5502_, 3, v___f_5498_);
lean_ctor_set(v___x_5502_, 4, v___f_5499_);
v___x_5503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5503_, 0, v___x_5502_);
lean_ctor_set(v___x_5503_, 1, v___f_5500_);
v___x_5504_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5505_, 0, v___x_5504_);
v___x_5506_ = l_instInhabitedOfMonad___redArg(v___x_5503_, v___x_5505_);
v___x_5507_ = lean_panic_fn_borrowed(v___x_5506_, v_msg_5493_);
lean_dec(v___x_5506_);
return v___x_5507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5508_, uint8_t v___x_5509_, lean_object* v_as_5510_, size_t v_sz_5511_, size_t v_i_5512_, lean_object* v_b_5513_){
_start:
{
lean_object* v_a_5515_; uint8_t v___x_5519_; 
v___x_5519_ = lean_usize_dec_lt(v_i_5512_, v_sz_5511_);
if (v___x_5519_ == 0)
{
return v_b_5513_;
}
else
{
lean_object* v_fst_5520_; lean_object* v_snd_5521_; lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5542_; 
v_fst_5520_ = lean_ctor_get(v_b_5513_, 0);
v_snd_5521_ = lean_ctor_get(v_b_5513_, 1);
v_isSharedCheck_5542_ = !lean_is_exclusive(v_b_5513_);
if (v_isSharedCheck_5542_ == 0)
{
v___x_5523_ = v_b_5513_;
v_isShared_5524_ = v_isSharedCheck_5542_;
goto v_resetjp_5522_;
}
else
{
lean_inc(v_snd_5521_);
lean_inc(v_fst_5520_);
lean_dec(v_b_5513_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5542_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v_a_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; 
v_a_5529_ = lean_array_uget_borrowed(v_as_5510_, v_i_5512_);
v___x_5530_ = lean_box(0);
v___x_5531_ = lean_array_get_borrowed(v___x_5530_, v___x_5508_, v_a_5529_);
if (lean_obj_tag(v___x_5531_) == 1)
{
lean_object* v_val_5532_; uint8_t v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; uint8_t v___x_5536_; 
v_val_5532_ = lean_ctor_get(v___x_5531_, 0);
v___x_5533_ = 0;
v___x_5534_ = lean_box(v___x_5533_);
v___x_5535_ = lean_array_get(v___x_5534_, v_fst_5520_, v_val_5532_);
lean_dec(v___x_5534_);
v___x_5536_ = lean_unbox(v___x_5535_);
lean_dec(v___x_5535_);
if (v___x_5536_ == 0)
{
if (v___x_5509_ == 0)
{
goto v___jp_5525_;
}
else
{
lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; 
lean_del_object(v___x_5523_);
lean_dec(v_snd_5521_);
v___x_5537_ = lean_box(v___x_5509_);
v___x_5538_ = lean_array_set(v_fst_5520_, v_val_5532_, v___x_5537_);
v___x_5539_ = lean_box(v___x_5509_);
v___x_5540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5540_, 0, v___x_5538_);
lean_ctor_set(v___x_5540_, 1, v___x_5539_);
v_a_5515_ = v___x_5540_;
goto v___jp_5514_;
}
}
else
{
goto v___jp_5525_;
}
}
else
{
lean_object* v___x_5541_; 
lean_del_object(v___x_5523_);
v___x_5541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5541_, 0, v_fst_5520_);
lean_ctor_set(v___x_5541_, 1, v_snd_5521_);
v_a_5515_ = v___x_5541_;
goto v___jp_5514_;
}
v___jp_5525_:
{
lean_object* v___x_5527_; 
if (v_isShared_5524_ == 0)
{
v___x_5527_ = v___x_5523_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_fst_5520_);
lean_ctor_set(v_reuseFailAlloc_5528_, 1, v_snd_5521_);
v___x_5527_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
v_a_5515_ = v___x_5527_;
goto v___jp_5514_;
}
}
}
}
v___jp_5514_:
{
size_t v___x_5516_; size_t v___x_5517_; 
v___x_5516_ = ((size_t)1ULL);
v___x_5517_ = lean_usize_add(v_i_5512_, v___x_5516_);
v_i_5512_ = v___x_5517_;
v_b_5513_ = v_a_5515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5543_, lean_object* v___x_5544_, lean_object* v_as_5545_, lean_object* v_sz_5546_, lean_object* v_i_5547_, lean_object* v_b_5548_){
_start:
{
uint8_t v___x_8295__boxed_5549_; size_t v_sz_boxed_5550_; size_t v_i_boxed_5551_; lean_object* v_res_5552_; 
v___x_8295__boxed_5549_ = lean_unbox(v___x_5544_);
v_sz_boxed_5550_ = lean_unbox_usize(v_sz_5546_);
lean_dec(v_sz_5546_);
v_i_boxed_5551_ = lean_unbox_usize(v_i_5547_);
lean_dec(v_i_5547_);
v_res_5552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5543_, v___x_8295__boxed_5549_, v_as_5545_, v_sz_boxed_5550_, v_i_boxed_5551_, v_b_5548_);
lean_dec_ref(v_as_5545_);
lean_dec_ref(v___x_5543_);
return v_res_5552_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5553_, lean_object* v___x_5554_, lean_object* v_fixedParamPerms_5555_, lean_object* v_next_5556_, lean_object* v_a_5557_, lean_object* v_b_5558_){
_start:
{
lean_object* v_a_5560_; uint8_t v___x_5564_; 
v___x_5564_ = lean_nat_dec_lt(v_a_5557_, v_upperBound_5553_);
if (v___x_5564_ == 0)
{
lean_dec(v_a_5557_);
return v_b_5558_;
}
else
{
lean_object* v_fst_5565_; lean_object* v_snd_5566_; lean_object* v___x_5568_; uint8_t v_isShared_5569_; uint8_t v_isSharedCheck_5602_; 
v_fst_5565_ = lean_ctor_get(v_b_5558_, 0);
v_snd_5566_ = lean_ctor_get(v_b_5558_, 1);
v_isSharedCheck_5602_ = !lean_is_exclusive(v_b_5558_);
if (v_isSharedCheck_5602_ == 0)
{
v___x_5568_ = v_b_5558_;
v_isShared_5569_ = v_isSharedCheck_5602_;
goto v_resetjp_5567_;
}
else
{
lean_inc(v_snd_5566_);
lean_inc(v_fst_5565_);
lean_dec(v_b_5558_);
v___x_5568_ = lean_box(0);
v_isShared_5569_ = v_isSharedCheck_5602_;
goto v_resetjp_5567_;
}
v_resetjp_5567_:
{
lean_object* v___x_5570_; 
v___x_5570_ = lean_array_fget_borrowed(v___x_5554_, v_a_5557_);
if (lean_obj_tag(v___x_5570_) == 1)
{
lean_object* v_val_5571_; uint8_t v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; uint8_t v___x_5575_; 
v_val_5571_ = lean_ctor_get(v___x_5570_, 0);
v___x_5572_ = 0;
v___x_5573_ = lean_box(v___x_5572_);
v___x_5574_ = lean_array_get(v___x_5573_, v_fst_5565_, v_val_5571_);
lean_dec(v___x_5573_);
v___x_5575_ = lean_unbox(v___x_5574_);
if (v___x_5575_ == 0)
{
lean_object* v___x_5577_; 
lean_dec(v___x_5574_);
if (v_isShared_5569_ == 0)
{
v___x_5577_ = v___x_5568_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_fst_5565_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v_snd_5566_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
v_a_5560_ = v___x_5577_;
goto v___jp_5559_;
}
}
else
{
lean_object* v_revDeps_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5584_; 
v_revDeps_5579_ = lean_ctor_get(v_fixedParamPerms_5555_, 2);
v___x_5580_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_5581_ = lean_array_get_borrowed(v___x_5580_, v_revDeps_5579_, v_next_5556_);
v___x_5582_ = lean_array_get_borrowed(v___x_5580_, v___x_5581_, v_a_5557_);
if (v_isShared_5569_ == 0)
{
v___x_5584_ = v___x_5568_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_fst_5565_);
lean_ctor_set(v_reuseFailAlloc_5598_, 1, v_snd_5566_);
v___x_5584_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
size_t v_sz_5585_; size_t v___x_5586_; uint8_t v___x_5587_; lean_object* v___x_5588_; lean_object* v_fst_5589_; lean_object* v_snd_5590_; lean_object* v___x_5592_; uint8_t v_isShared_5593_; uint8_t v_isSharedCheck_5597_; 
v_sz_5585_ = lean_array_size(v___x_5582_);
v___x_5586_ = ((size_t)0ULL);
v___x_5587_ = lean_unbox(v___x_5574_);
lean_dec(v___x_5574_);
v___x_5588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5554_, v___x_5587_, v___x_5582_, v_sz_5585_, v___x_5586_, v___x_5584_);
v_fst_5589_ = lean_ctor_get(v___x_5588_, 0);
v_snd_5590_ = lean_ctor_get(v___x_5588_, 1);
v_isSharedCheck_5597_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5597_ == 0)
{
v___x_5592_ = v___x_5588_;
v_isShared_5593_ = v_isSharedCheck_5597_;
goto v_resetjp_5591_;
}
else
{
lean_inc(v_snd_5590_);
lean_inc(v_fst_5589_);
lean_dec(v___x_5588_);
v___x_5592_ = lean_box(0);
v_isShared_5593_ = v_isSharedCheck_5597_;
goto v_resetjp_5591_;
}
v_resetjp_5591_:
{
lean_object* v___x_5595_; 
if (v_isShared_5593_ == 0)
{
v___x_5595_ = v___x_5592_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_fst_5589_);
lean_ctor_set(v_reuseFailAlloc_5596_, 1, v_snd_5590_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
v_a_5560_ = v___x_5595_;
goto v___jp_5559_;
}
}
}
}
}
else
{
lean_object* v___x_5600_; 
if (v_isShared_5569_ == 0)
{
v___x_5600_ = v___x_5568_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_fst_5565_);
lean_ctor_set(v_reuseFailAlloc_5601_, 1, v_snd_5566_);
v___x_5600_ = v_reuseFailAlloc_5601_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
v_a_5560_ = v___x_5600_;
goto v___jp_5559_;
}
}
}
}
v___jp_5559_:
{
lean_object* v___x_5561_; lean_object* v___x_5562_; 
v___x_5561_ = lean_unsigned_to_nat(1u);
v___x_5562_ = lean_nat_add(v_a_5557_, v___x_5561_);
lean_dec(v_a_5557_);
v_a_5557_ = v___x_5562_;
v_b_5558_ = v_a_5560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5603_, lean_object* v___x_5604_, lean_object* v_fixedParamPerms_5605_, lean_object* v_next_5606_, lean_object* v_a_5607_, lean_object* v_b_5608_){
_start:
{
lean_object* v_res_5609_; 
v_res_5609_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5603_, v___x_5604_, v_fixedParamPerms_5605_, v_next_5606_, v_a_5607_, v_b_5608_);
lean_dec(v_next_5606_);
lean_dec_ref(v_fixedParamPerms_5605_);
lean_dec_ref(v___x_5604_);
lean_dec(v_upperBound_5603_);
return v_res_5609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5610_, lean_object* v___x_5611_, lean_object* v_fixedParamPerms_5612_, lean_object* v_a_5613_, lean_object* v_b_5614_){
_start:
{
uint8_t v___x_5615_; 
v___x_5615_ = lean_nat_dec_lt(v_a_5613_, v_upperBound_5610_);
if (v___x_5615_ == 0)
{
lean_dec(v_a_5613_);
return v_b_5614_;
}
else
{
lean_object* v_fst_5616_; lean_object* v_snd_5617_; lean_object* v___x_5619_; uint8_t v_isShared_5620_; uint8_t v_isSharedCheck_5640_; 
v_fst_5616_ = lean_ctor_get(v_b_5614_, 0);
v_snd_5617_ = lean_ctor_get(v_b_5614_, 1);
v_isSharedCheck_5640_ = !lean_is_exclusive(v_b_5614_);
if (v_isSharedCheck_5640_ == 0)
{
v___x_5619_ = v_b_5614_;
v_isShared_5620_ = v_isSharedCheck_5640_;
goto v_resetjp_5618_;
}
else
{
lean_inc(v_snd_5617_);
lean_inc(v_fst_5616_);
lean_dec(v_b_5614_);
v___x_5619_ = lean_box(0);
v_isShared_5620_ = v_isSharedCheck_5640_;
goto v_resetjp_5618_;
}
v_resetjp_5618_:
{
lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5625_; 
v___x_5621_ = lean_array_fget_borrowed(v___x_5611_, v_a_5613_);
v___x_5622_ = lean_array_get_size(v___x_5621_);
v___x_5623_ = lean_unsigned_to_nat(0u);
if (v_isShared_5620_ == 0)
{
v___x_5625_ = v___x_5619_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v_fst_5616_);
lean_ctor_set(v_reuseFailAlloc_5639_, 1, v_snd_5617_);
v___x_5625_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
lean_object* v___x_5626_; lean_object* v_fst_5627_; lean_object* v_snd_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5638_; 
v___x_5626_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5622_, v___x_5621_, v_fixedParamPerms_5612_, v_a_5613_, v___x_5623_, v___x_5625_);
v_fst_5627_ = lean_ctor_get(v___x_5626_, 0);
v_snd_5628_ = lean_ctor_get(v___x_5626_, 1);
v_isSharedCheck_5638_ = !lean_is_exclusive(v___x_5626_);
if (v_isSharedCheck_5638_ == 0)
{
v___x_5630_ = v___x_5626_;
v_isShared_5631_ = v_isSharedCheck_5638_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_snd_5628_);
lean_inc(v_fst_5627_);
lean_dec(v___x_5626_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5638_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
lean_object* v___x_5633_; 
if (v_isShared_5631_ == 0)
{
v___x_5633_ = v___x_5630_;
goto v_reusejp_5632_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_fst_5627_);
lean_ctor_set(v_reuseFailAlloc_5637_, 1, v_snd_5628_);
v___x_5633_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5632_;
}
v_reusejp_5632_:
{
lean_object* v___x_5634_; lean_object* v___x_5635_; 
v___x_5634_ = lean_unsigned_to_nat(1u);
v___x_5635_ = lean_nat_add(v_a_5613_, v___x_5634_);
lean_dec(v_a_5613_);
v_a_5613_ = v___x_5635_;
v_b_5614_ = v___x_5633_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5641_, lean_object* v___x_5642_, lean_object* v_fixedParamPerms_5643_, lean_object* v_a_5644_, lean_object* v_b_5645_){
_start:
{
lean_object* v_res_5646_; 
v_res_5646_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5641_, v___x_5642_, v_fixedParamPerms_5643_, v_a_5644_, v_b_5645_);
lean_dec_ref(v_fixedParamPerms_5643_);
lean_dec_ref(v___x_5642_);
lean_dec(v_upperBound_5641_);
return v_res_5646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5647_, lean_object* v___x_5648_, lean_object* v_fixedParamPerms_5649_, lean_object* v_a_5650_){
_start:
{
lean_object* v_snd_5651_; uint8_t v___x_5652_; 
v_snd_5651_ = lean_ctor_get(v_a_5650_, 1);
v___x_5652_ = lean_unbox(v_snd_5651_);
if (v___x_5652_ == 0)
{
lean_object* v_fst_5653_; lean_object* v___x_5655_; uint8_t v_isShared_5656_; uint8_t v_isSharedCheck_5660_; 
lean_inc(v_snd_5651_);
v_fst_5653_ = lean_ctor_get(v_a_5650_, 0);
v_isSharedCheck_5660_ = !lean_is_exclusive(v_a_5650_);
if (v_isSharedCheck_5660_ == 0)
{
lean_object* v_unused_5661_; 
v_unused_5661_ = lean_ctor_get(v_a_5650_, 1);
lean_dec(v_unused_5661_);
v___x_5655_ = v_a_5650_;
v_isShared_5656_ = v_isSharedCheck_5660_;
goto v_resetjp_5654_;
}
else
{
lean_inc(v_fst_5653_);
lean_dec(v_a_5650_);
v___x_5655_ = lean_box(0);
v_isShared_5656_ = v_isSharedCheck_5660_;
goto v_resetjp_5654_;
}
v_resetjp_5654_:
{
lean_object* v___x_5658_; 
if (v_isShared_5656_ == 0)
{
v___x_5658_ = v___x_5655_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_fst_5653_);
lean_ctor_set(v_reuseFailAlloc_5659_, 1, v_snd_5651_);
v___x_5658_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
return v___x_5658_;
}
}
}
else
{
lean_object* v_fst_5662_; lean_object* v___x_5664_; uint8_t v_isShared_5665_; uint8_t v_isSharedCheck_5683_; 
v_fst_5662_ = lean_ctor_get(v_a_5650_, 0);
v_isSharedCheck_5683_ = !lean_is_exclusive(v_a_5650_);
if (v_isSharedCheck_5683_ == 0)
{
lean_object* v_unused_5684_; 
v_unused_5684_ = lean_ctor_get(v_a_5650_, 1);
lean_dec(v_unused_5684_);
v___x_5664_ = v_a_5650_;
v_isShared_5665_ = v_isSharedCheck_5683_;
goto v_resetjp_5663_;
}
else
{
lean_inc(v_fst_5662_);
lean_dec(v_a_5650_);
v___x_5664_ = lean_box(0);
v_isShared_5665_ = v_isSharedCheck_5683_;
goto v_resetjp_5663_;
}
v_resetjp_5663_:
{
uint8_t v_changed_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5670_; 
v_changed_5666_ = 0;
v___x_5667_ = lean_unsigned_to_nat(0u);
v___x_5668_ = lean_box(v_changed_5666_);
if (v_isShared_5665_ == 0)
{
lean_ctor_set(v___x_5664_, 1, v___x_5668_);
v___x_5670_ = v___x_5664_;
goto v_reusejp_5669_;
}
else
{
lean_object* v_reuseFailAlloc_5682_; 
v_reuseFailAlloc_5682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_fst_5662_);
lean_ctor_set(v_reuseFailAlloc_5682_, 1, v___x_5668_);
v___x_5670_ = v_reuseFailAlloc_5682_;
goto v_reusejp_5669_;
}
v_reusejp_5669_:
{
lean_object* v___x_5671_; lean_object* v_fst_5672_; lean_object* v_snd_5673_; lean_object* v___x_5675_; uint8_t v_isShared_5676_; uint8_t v_isSharedCheck_5681_; 
v___x_5671_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5647_, v___x_5648_, v_fixedParamPerms_5649_, v___x_5667_, v___x_5670_);
v_fst_5672_ = lean_ctor_get(v___x_5671_, 0);
v_snd_5673_ = lean_ctor_get(v___x_5671_, 1);
v_isSharedCheck_5681_ = !lean_is_exclusive(v___x_5671_);
if (v_isSharedCheck_5681_ == 0)
{
v___x_5675_ = v___x_5671_;
v_isShared_5676_ = v_isSharedCheck_5681_;
goto v_resetjp_5674_;
}
else
{
lean_inc(v_snd_5673_);
lean_inc(v_fst_5672_);
lean_dec(v___x_5671_);
v___x_5675_ = lean_box(0);
v_isShared_5676_ = v_isSharedCheck_5681_;
goto v_resetjp_5674_;
}
v_resetjp_5674_:
{
lean_object* v___x_5678_; 
if (v_isShared_5676_ == 0)
{
v___x_5678_ = v___x_5675_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_fst_5672_);
lean_ctor_set(v_reuseFailAlloc_5680_, 1, v_snd_5673_);
v___x_5678_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
v_a_5650_ = v___x_5678_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5685_, lean_object* v___x_5686_, lean_object* v_fixedParamPerms_5687_, lean_object* v_a_5688_){
_start:
{
lean_object* v_res_5689_; 
v_res_5689_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5685_, v___x_5686_, v_fixedParamPerms_5687_, v_a_5688_);
lean_dec_ref(v_fixedParamPerms_5687_);
lean_dec_ref(v___x_5686_);
lean_dec(v___x_5685_);
return v_res_5689_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5690_, lean_object* v_a_5691_, lean_object* v_b_5692_){
_start:
{
lean_object* v_a_5694_; uint8_t v___x_5698_; 
v___x_5698_ = lean_nat_dec_lt(v_a_5691_, v_upperBound_5690_);
if (v___x_5698_ == 0)
{
lean_dec(v_a_5691_);
return v_b_5692_;
}
else
{
lean_object* v_snd_5699_; lean_object* v_snd_5700_; lean_object* v_snd_5701_; lean_object* v_snd_5702_; lean_object* v_fst_5703_; lean_object* v___x_5705_; uint8_t v_isShared_5706_; uint8_t v_isSharedCheck_5815_; 
v_snd_5699_ = lean_ctor_get(v_b_5692_, 1);
lean_inc(v_snd_5699_);
v_snd_5700_ = lean_ctor_get(v_snd_5699_, 1);
lean_inc(v_snd_5700_);
v_snd_5701_ = lean_ctor_get(v_snd_5700_, 1);
lean_inc(v_snd_5701_);
v_snd_5702_ = lean_ctor_get(v_snd_5701_, 1);
lean_inc(v_snd_5702_);
v_fst_5703_ = lean_ctor_get(v_b_5692_, 0);
v_isSharedCheck_5815_ = !lean_is_exclusive(v_b_5692_);
if (v_isSharedCheck_5815_ == 0)
{
lean_object* v_unused_5816_; 
v_unused_5816_ = lean_ctor_get(v_b_5692_, 1);
lean_dec(v_unused_5816_);
v___x_5705_ = v_b_5692_;
v_isShared_5706_ = v_isSharedCheck_5815_;
goto v_resetjp_5704_;
}
else
{
lean_inc(v_fst_5703_);
lean_dec(v_b_5692_);
v___x_5705_ = lean_box(0);
v_isShared_5706_ = v_isSharedCheck_5815_;
goto v_resetjp_5704_;
}
v_resetjp_5704_:
{
lean_object* v_fst_5707_; lean_object* v___x_5709_; uint8_t v_isShared_5710_; uint8_t v_isSharedCheck_5813_; 
v_fst_5707_ = lean_ctor_get(v_snd_5699_, 0);
v_isSharedCheck_5813_ = !lean_is_exclusive(v_snd_5699_);
if (v_isSharedCheck_5813_ == 0)
{
lean_object* v_unused_5814_; 
v_unused_5814_ = lean_ctor_get(v_snd_5699_, 1);
lean_dec(v_unused_5814_);
v___x_5709_ = v_snd_5699_;
v_isShared_5710_ = v_isSharedCheck_5813_;
goto v_resetjp_5708_;
}
else
{
lean_inc(v_fst_5707_);
lean_dec(v_snd_5699_);
v___x_5709_ = lean_box(0);
v_isShared_5710_ = v_isSharedCheck_5813_;
goto v_resetjp_5708_;
}
v_resetjp_5708_:
{
lean_object* v_fst_5711_; lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5811_; 
v_fst_5711_ = lean_ctor_get(v_snd_5700_, 0);
v_isSharedCheck_5811_ = !lean_is_exclusive(v_snd_5700_);
if (v_isSharedCheck_5811_ == 0)
{
lean_object* v_unused_5812_; 
v_unused_5812_ = lean_ctor_get(v_snd_5700_, 1);
lean_dec(v_unused_5812_);
v___x_5713_ = v_snd_5700_;
v_isShared_5714_ = v_isSharedCheck_5811_;
goto v_resetjp_5712_;
}
else
{
lean_inc(v_fst_5711_);
lean_dec(v_snd_5700_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5811_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
lean_object* v_fst_5715_; lean_object* v___x_5717_; uint8_t v_isShared_5718_; uint8_t v_isSharedCheck_5809_; 
v_fst_5715_ = lean_ctor_get(v_snd_5701_, 0);
v_isSharedCheck_5809_ = !lean_is_exclusive(v_snd_5701_);
if (v_isSharedCheck_5809_ == 0)
{
lean_object* v_unused_5810_; 
v_unused_5810_ = lean_ctor_get(v_snd_5701_, 1);
lean_dec(v_unused_5810_);
v___x_5717_ = v_snd_5701_;
v_isShared_5718_ = v_isSharedCheck_5809_;
goto v_resetjp_5716_;
}
else
{
lean_inc(v_fst_5715_);
lean_dec(v_snd_5701_);
v___x_5717_ = lean_box(0);
v_isShared_5718_ = v_isSharedCheck_5809_;
goto v_resetjp_5716_;
}
v_resetjp_5716_:
{
lean_object* v_array_5719_; lean_object* v_start_5720_; lean_object* v_stop_5721_; uint8_t v___x_5722_; 
v_array_5719_ = lean_ctor_get(v_snd_5702_, 0);
v_start_5720_ = lean_ctor_get(v_snd_5702_, 1);
v_stop_5721_ = lean_ctor_get(v_snd_5702_, 2);
v___x_5722_ = lean_nat_dec_lt(v_start_5720_, v_stop_5721_);
if (v___x_5722_ == 0)
{
lean_object* v___x_5724_; 
lean_dec(v_a_5691_);
if (v_isShared_5718_ == 0)
{
v___x_5724_ = v___x_5717_;
goto v_reusejp_5723_;
}
else
{
lean_object* v_reuseFailAlloc_5734_; 
v_reuseFailAlloc_5734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5734_, 0, v_fst_5715_);
lean_ctor_set(v_reuseFailAlloc_5734_, 1, v_snd_5702_);
v___x_5724_ = v_reuseFailAlloc_5734_;
goto v_reusejp_5723_;
}
v_reusejp_5723_:
{
lean_object* v___x_5726_; 
if (v_isShared_5714_ == 0)
{
lean_ctor_set(v___x_5713_, 1, v___x_5724_);
v___x_5726_ = v___x_5713_;
goto v_reusejp_5725_;
}
else
{
lean_object* v_reuseFailAlloc_5733_; 
v_reuseFailAlloc_5733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5733_, 0, v_fst_5711_);
lean_ctor_set(v_reuseFailAlloc_5733_, 1, v___x_5724_);
v___x_5726_ = v_reuseFailAlloc_5733_;
goto v_reusejp_5725_;
}
v_reusejp_5725_:
{
lean_object* v___x_5728_; 
if (v_isShared_5710_ == 0)
{
lean_ctor_set(v___x_5709_, 1, v___x_5726_);
v___x_5728_ = v___x_5709_;
goto v_reusejp_5727_;
}
else
{
lean_object* v_reuseFailAlloc_5732_; 
v_reuseFailAlloc_5732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_fst_5707_);
lean_ctor_set(v_reuseFailAlloc_5732_, 1, v___x_5726_);
v___x_5728_ = v_reuseFailAlloc_5732_;
goto v_reusejp_5727_;
}
v_reusejp_5727_:
{
lean_object* v___x_5730_; 
if (v_isShared_5706_ == 0)
{
lean_ctor_set(v___x_5705_, 1, v___x_5728_);
v___x_5730_ = v___x_5705_;
goto v_reusejp_5729_;
}
else
{
lean_object* v_reuseFailAlloc_5731_; 
v_reuseFailAlloc_5731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5731_, 0, v_fst_5703_);
lean_ctor_set(v_reuseFailAlloc_5731_, 1, v___x_5728_);
v___x_5730_ = v_reuseFailAlloc_5731_;
goto v_reusejp_5729_;
}
v_reusejp_5729_:
{
return v___x_5730_;
}
}
}
}
}
else
{
lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5805_; 
lean_inc(v_stop_5721_);
lean_inc(v_start_5720_);
lean_inc_ref(v_array_5719_);
v_isSharedCheck_5805_ = !lean_is_exclusive(v_snd_5702_);
if (v_isSharedCheck_5805_ == 0)
{
lean_object* v_unused_5806_; lean_object* v_unused_5807_; lean_object* v_unused_5808_; 
v_unused_5806_ = lean_ctor_get(v_snd_5702_, 2);
lean_dec(v_unused_5806_);
v_unused_5807_ = lean_ctor_get(v_snd_5702_, 1);
lean_dec(v_unused_5807_);
v_unused_5808_ = lean_ctor_get(v_snd_5702_, 0);
lean_dec(v_unused_5808_);
v___x_5736_ = v_snd_5702_;
v_isShared_5737_ = v_isSharedCheck_5805_;
goto v_resetjp_5735_;
}
else
{
lean_dec(v_snd_5702_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5805_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v_array_5738_; lean_object* v_start_5739_; lean_object* v_stop_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5745_; 
v_array_5738_ = lean_ctor_get(v_fst_5715_, 0);
v_start_5739_ = lean_ctor_get(v_fst_5715_, 1);
v_stop_5740_ = lean_ctor_get(v_fst_5715_, 2);
v___x_5741_ = lean_array_fget(v_array_5719_, v_start_5720_);
v___x_5742_ = lean_unsigned_to_nat(1u);
v___x_5743_ = lean_nat_add(v_start_5720_, v___x_5742_);
lean_dec(v_start_5720_);
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 1, v___x_5743_);
v___x_5745_ = v___x_5736_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5804_; 
v_reuseFailAlloc_5804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5804_, 0, v_array_5719_);
lean_ctor_set(v_reuseFailAlloc_5804_, 1, v___x_5743_);
lean_ctor_set(v_reuseFailAlloc_5804_, 2, v_stop_5721_);
v___x_5745_ = v_reuseFailAlloc_5804_;
goto v_reusejp_5744_;
}
v_reusejp_5744_:
{
uint8_t v___x_5746_; 
v___x_5746_ = lean_nat_dec_lt(v_start_5739_, v_stop_5740_);
if (v___x_5746_ == 0)
{
lean_object* v___x_5748_; 
lean_dec(v___x_5741_);
lean_dec(v_a_5691_);
if (v_isShared_5718_ == 0)
{
lean_ctor_set(v___x_5717_, 1, v___x_5745_);
v___x_5748_ = v___x_5717_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5758_; 
v_reuseFailAlloc_5758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5758_, 0, v_fst_5715_);
lean_ctor_set(v_reuseFailAlloc_5758_, 1, v___x_5745_);
v___x_5748_ = v_reuseFailAlloc_5758_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
lean_object* v___x_5750_; 
if (v_isShared_5714_ == 0)
{
lean_ctor_set(v___x_5713_, 1, v___x_5748_);
v___x_5750_ = v___x_5713_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v_fst_5711_);
lean_ctor_set(v_reuseFailAlloc_5757_, 1, v___x_5748_);
v___x_5750_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
lean_object* v___x_5752_; 
if (v_isShared_5710_ == 0)
{
lean_ctor_set(v___x_5709_, 1, v___x_5750_);
v___x_5752_ = v___x_5709_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v_fst_5707_);
lean_ctor_set(v_reuseFailAlloc_5756_, 1, v___x_5750_);
v___x_5752_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
lean_object* v___x_5754_; 
if (v_isShared_5706_ == 0)
{
lean_ctor_set(v___x_5705_, 1, v___x_5752_);
v___x_5754_ = v___x_5705_;
goto v_reusejp_5753_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v_fst_5703_);
lean_ctor_set(v_reuseFailAlloc_5755_, 1, v___x_5752_);
v___x_5754_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5753_;
}
v_reusejp_5753_:
{
return v___x_5754_;
}
}
}
}
}
else
{
lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5800_; 
lean_inc(v_stop_5740_);
lean_inc(v_start_5739_);
lean_inc_ref(v_array_5738_);
v_isSharedCheck_5800_ = !lean_is_exclusive(v_fst_5715_);
if (v_isSharedCheck_5800_ == 0)
{
lean_object* v_unused_5801_; lean_object* v_unused_5802_; lean_object* v_unused_5803_; 
v_unused_5801_ = lean_ctor_get(v_fst_5715_, 2);
lean_dec(v_unused_5801_);
v_unused_5802_ = lean_ctor_get(v_fst_5715_, 1);
lean_dec(v_unused_5802_);
v_unused_5803_ = lean_ctor_get(v_fst_5715_, 0);
lean_dec(v_unused_5803_);
v___x_5760_ = v_fst_5715_;
v_isShared_5761_ = v_isSharedCheck_5800_;
goto v_resetjp_5759_;
}
else
{
lean_dec(v_fst_5715_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5800_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5765_; 
v___x_5762_ = lean_array_fget(v_array_5738_, v_start_5739_);
v___x_5763_ = lean_nat_add(v_start_5739_, v___x_5742_);
lean_dec(v_start_5739_);
if (v_isShared_5761_ == 0)
{
lean_ctor_set(v___x_5760_, 1, v___x_5763_);
v___x_5765_ = v___x_5760_;
goto v_reusejp_5764_;
}
else
{
lean_object* v_reuseFailAlloc_5799_; 
v_reuseFailAlloc_5799_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5799_, 0, v_array_5738_);
lean_ctor_set(v_reuseFailAlloc_5799_, 1, v___x_5763_);
lean_ctor_set(v_reuseFailAlloc_5799_, 2, v_stop_5740_);
v___x_5765_ = v_reuseFailAlloc_5799_;
goto v_reusejp_5764_;
}
v_reusejp_5764_:
{
uint8_t v___x_5766_; 
v___x_5766_ = lean_unbox(v___x_5762_);
lean_dec(v___x_5762_);
if (v___x_5766_ == 0)
{
lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5772_; 
v___x_5767_ = lean_array_get_size(v_fst_5711_);
v___x_5768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5768_, 0, v___x_5767_);
v___x_5769_ = lean_array_push(v_fst_5703_, v___x_5768_);
v___x_5770_ = lean_array_push(v_fst_5711_, v___x_5741_);
if (v_isShared_5718_ == 0)
{
lean_ctor_set(v___x_5717_, 1, v___x_5745_);
lean_ctor_set(v___x_5717_, 0, v___x_5765_);
v___x_5772_ = v___x_5717_;
goto v_reusejp_5771_;
}
else
{
lean_object* v_reuseFailAlloc_5782_; 
v_reuseFailAlloc_5782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5782_, 0, v___x_5765_);
lean_ctor_set(v_reuseFailAlloc_5782_, 1, v___x_5745_);
v___x_5772_ = v_reuseFailAlloc_5782_;
goto v_reusejp_5771_;
}
v_reusejp_5771_:
{
lean_object* v___x_5774_; 
if (v_isShared_5714_ == 0)
{
lean_ctor_set(v___x_5713_, 1, v___x_5772_);
lean_ctor_set(v___x_5713_, 0, v___x_5770_);
v___x_5774_ = v___x_5713_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v___x_5770_);
lean_ctor_set(v_reuseFailAlloc_5781_, 1, v___x_5772_);
v___x_5774_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
lean_object* v___x_5776_; 
if (v_isShared_5710_ == 0)
{
lean_ctor_set(v___x_5709_, 1, v___x_5774_);
v___x_5776_ = v___x_5709_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_fst_5707_);
lean_ctor_set(v_reuseFailAlloc_5780_, 1, v___x_5774_);
v___x_5776_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
lean_object* v___x_5778_; 
if (v_isShared_5706_ == 0)
{
lean_ctor_set(v___x_5705_, 1, v___x_5776_);
lean_ctor_set(v___x_5705_, 0, v___x_5769_);
v___x_5778_ = v___x_5705_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5779_; 
v_reuseFailAlloc_5779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5779_, 0, v___x_5769_);
lean_ctor_set(v_reuseFailAlloc_5779_, 1, v___x_5776_);
v___x_5778_ = v_reuseFailAlloc_5779_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
v_a_5694_ = v___x_5778_;
goto v___jp_5693_;
}
}
}
}
}
else
{
lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5788_; 
v___x_5783_ = lean_box(0);
v___x_5784_ = lean_array_push(v_fst_5703_, v___x_5783_);
v___x_5785_ = l_Lean_Expr_fvarId_x21(v___x_5741_);
lean_dec(v___x_5741_);
v___x_5786_ = lean_array_push(v_fst_5707_, v___x_5785_);
if (v_isShared_5718_ == 0)
{
lean_ctor_set(v___x_5717_, 1, v___x_5745_);
lean_ctor_set(v___x_5717_, 0, v___x_5765_);
v___x_5788_ = v___x_5717_;
goto v_reusejp_5787_;
}
else
{
lean_object* v_reuseFailAlloc_5798_; 
v_reuseFailAlloc_5798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5798_, 0, v___x_5765_);
lean_ctor_set(v_reuseFailAlloc_5798_, 1, v___x_5745_);
v___x_5788_ = v_reuseFailAlloc_5798_;
goto v_reusejp_5787_;
}
v_reusejp_5787_:
{
lean_object* v___x_5790_; 
if (v_isShared_5714_ == 0)
{
lean_ctor_set(v___x_5713_, 1, v___x_5788_);
v___x_5790_ = v___x_5713_;
goto v_reusejp_5789_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v_fst_5711_);
lean_ctor_set(v_reuseFailAlloc_5797_, 1, v___x_5788_);
v___x_5790_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5789_;
}
v_reusejp_5789_:
{
lean_object* v___x_5792_; 
if (v_isShared_5710_ == 0)
{
lean_ctor_set(v___x_5709_, 1, v___x_5790_);
lean_ctor_set(v___x_5709_, 0, v___x_5786_);
v___x_5792_ = v___x_5709_;
goto v_reusejp_5791_;
}
else
{
lean_object* v_reuseFailAlloc_5796_; 
v_reuseFailAlloc_5796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5796_, 0, v___x_5786_);
lean_ctor_set(v_reuseFailAlloc_5796_, 1, v___x_5790_);
v___x_5792_ = v_reuseFailAlloc_5796_;
goto v_reusejp_5791_;
}
v_reusejp_5791_:
{
lean_object* v___x_5794_; 
if (v_isShared_5706_ == 0)
{
lean_ctor_set(v___x_5705_, 1, v___x_5792_);
lean_ctor_set(v___x_5705_, 0, v___x_5784_);
v___x_5794_ = v___x_5705_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v___x_5784_);
lean_ctor_set(v_reuseFailAlloc_5795_, 1, v___x_5792_);
v___x_5794_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5793_;
}
v_reusejp_5793_:
{
v_a_5694_ = v___x_5794_;
goto v___jp_5693_;
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
}
}
}
}
}
v___jp_5693_:
{
lean_object* v___x_5695_; lean_object* v___x_5696_; 
v___x_5695_ = lean_unsigned_to_nat(1u);
v___x_5696_ = lean_nat_add(v_a_5691_, v___x_5695_);
lean_dec(v_a_5691_);
v_a_5691_ = v___x_5696_;
v_b_5692_ = v_a_5694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5817_, lean_object* v_a_5818_, lean_object* v_b_5819_){
_start:
{
lean_object* v_res_5820_; 
v_res_5820_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5817_, v_a_5818_, v_b_5819_);
lean_dec(v_upperBound_5817_);
return v_res_5820_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5821_, size_t v_i_5822_, size_t v_stop_5823_){
_start:
{
uint8_t v___x_5824_; 
v___x_5824_ = lean_usize_dec_eq(v_i_5822_, v_stop_5823_);
if (v___x_5824_ == 0)
{
uint8_t v___x_5825_; lean_object* v___x_5826_; uint8_t v___x_5827_; 
v___x_5825_ = 1;
v___x_5826_ = lean_array_uget_borrowed(v_as_5821_, v_i_5822_);
v___x_5827_ = l_Lean_Expr_isFVar(v___x_5826_);
if (v___x_5827_ == 0)
{
return v___x_5825_;
}
else
{
if (v___x_5824_ == 0)
{
size_t v___x_5828_; size_t v___x_5829_; 
v___x_5828_ = ((size_t)1ULL);
v___x_5829_ = lean_usize_add(v_i_5822_, v___x_5828_);
v_i_5822_ = v___x_5829_;
goto _start;
}
else
{
return v___x_5825_;
}
}
}
else
{
uint8_t v___x_5831_; 
v___x_5831_ = 0;
return v___x_5831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5832_, lean_object* v_i_5833_, lean_object* v_stop_5834_){
_start:
{
size_t v_i_boxed_5835_; size_t v_stop_boxed_5836_; uint8_t v_res_5837_; lean_object* v_r_5838_; 
v_i_boxed_5835_ = lean_unbox_usize(v_i_5833_);
lean_dec(v_i_5833_);
v_stop_boxed_5836_ = lean_unbox_usize(v_stop_5834_);
lean_dec(v_stop_5834_);
v_res_5837_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5832_, v_i_boxed_5835_, v_stop_boxed_5836_);
lean_dec_ref(v_as_5832_);
v_r_5838_ = lean_box(v_res_5837_);
return v_r_5838_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; 
v___x_5841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5842_ = lean_unsigned_to_nat(6u);
v___x_5843_ = lean_unsigned_to_nat(463u);
v___x_5844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5845_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5846_ = l_mkPanicMessageWithDecl(v___x_5845_, v___x_5844_, v___x_5843_, v___x_5842_, v___x_5841_);
return v___x_5846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5847_, lean_object* v_as_5848_, size_t v_sz_5849_, size_t v_i_5850_, lean_object* v_b_5851_){
_start:
{
lean_object* v_a_5853_; uint8_t v___x_5857_; 
v___x_5857_ = lean_usize_dec_lt(v_i_5850_, v_sz_5849_);
if (v___x_5857_ == 0)
{
return v_b_5851_;
}
else
{
lean_object* v_a_5858_; lean_object* v___x_5859_; uint8_t v_changed_5860_; 
v_a_5858_ = lean_array_uget_borrowed(v_as_5848_, v_i_5850_);
v___x_5859_ = lean_array_get_size(v___x_5847_);
v_changed_5860_ = lean_nat_dec_lt(v_a_5858_, v___x_5859_);
if (v_changed_5860_ == 0)
{
lean_object* v___x_5861_; lean_object* v___x_5862_; 
lean_dec_ref(v_b_5851_);
v___x_5861_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5862_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5861_);
if (lean_obj_tag(v___x_5862_) == 0)
{
lean_object* v_a_5863_; 
v_a_5863_ = lean_ctor_get(v___x_5862_, 0);
lean_inc(v_a_5863_);
lean_dec_ref_known(v___x_5862_, 1);
return v_a_5863_;
}
else
{
lean_object* v_a_5864_; 
v_a_5864_ = lean_ctor_get(v___x_5862_, 0);
lean_inc(v_a_5864_);
lean_dec_ref_known(v___x_5862_, 1);
v_a_5853_ = v_a_5864_;
goto v___jp_5852_;
}
}
else
{
lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5865_ = lean_box(0);
v___x_5866_ = lean_array_get_borrowed(v___x_5865_, v___x_5847_, v_a_5858_);
if (lean_obj_tag(v___x_5866_) == 1)
{
lean_object* v_val_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; 
v_val_5867_ = lean_ctor_get(v___x_5866_, 0);
v___x_5868_ = lean_box(v_changed_5860_);
v___x_5869_ = lean_array_set(v_b_5851_, v_val_5867_, v___x_5868_);
v_a_5853_ = v___x_5869_;
goto v___jp_5852_;
}
else
{
v_a_5853_ = v_b_5851_;
goto v___jp_5852_;
}
}
}
v___jp_5852_:
{
size_t v___x_5854_; size_t v___x_5855_; 
v___x_5854_ = ((size_t)1ULL);
v___x_5855_ = lean_usize_add(v_i_5850_, v___x_5854_);
v_i_5850_ = v___x_5855_;
v_b_5851_ = v_a_5853_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5870_, lean_object* v_as_5871_, lean_object* v_sz_5872_, lean_object* v_i_5873_, lean_object* v_b_5874_){
_start:
{
size_t v_sz_boxed_5875_; size_t v_i_boxed_5876_; lean_object* v_res_5877_; 
v_sz_boxed_5875_ = lean_unbox_usize(v_sz_5872_);
lean_dec(v_sz_5872_);
v_i_boxed_5876_ = lean_unbox_usize(v_i_5873_);
lean_dec(v_i_5873_);
v_res_5877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5870_, v_as_5871_, v_sz_boxed_5875_, v_i_boxed_5876_, v_b_5874_);
lean_dec_ref(v_as_5871_);
lean_dec_ref(v___x_5870_);
return v_res_5877_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5878_, lean_object* v_a_5879_, lean_object* v_b_5880_){
_start:
{
uint8_t v___x_5881_; 
v___x_5881_ = lean_nat_dec_lt(v_a_5879_, v_upperBound_5878_);
if (v___x_5881_ == 0)
{
lean_dec(v_a_5879_);
return v_b_5880_;
}
else
{
lean_object* v_snd_5882_; lean_object* v_snd_5883_; lean_object* v_fst_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5950_; 
v_snd_5882_ = lean_ctor_get(v_b_5880_, 1);
lean_inc(v_snd_5882_);
v_snd_5883_ = lean_ctor_get(v_snd_5882_, 1);
lean_inc(v_snd_5883_);
v_fst_5884_ = lean_ctor_get(v_b_5880_, 0);
v_isSharedCheck_5950_ = !lean_is_exclusive(v_b_5880_);
if (v_isSharedCheck_5950_ == 0)
{
lean_object* v_unused_5951_; 
v_unused_5951_ = lean_ctor_get(v_b_5880_, 1);
lean_dec(v_unused_5951_);
v___x_5886_ = v_b_5880_;
v_isShared_5887_ = v_isSharedCheck_5950_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_fst_5884_);
lean_dec(v_b_5880_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_5950_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
lean_object* v_fst_5888_; lean_object* v___x_5890_; uint8_t v_isShared_5891_; uint8_t v_isSharedCheck_5948_; 
v_fst_5888_ = lean_ctor_get(v_snd_5882_, 0);
v_isSharedCheck_5948_ = !lean_is_exclusive(v_snd_5882_);
if (v_isSharedCheck_5948_ == 0)
{
lean_object* v_unused_5949_; 
v_unused_5949_ = lean_ctor_get(v_snd_5882_, 1);
lean_dec(v_unused_5949_);
v___x_5890_ = v_snd_5882_;
v_isShared_5891_ = v_isSharedCheck_5948_;
goto v_resetjp_5889_;
}
else
{
lean_inc(v_fst_5888_);
lean_dec(v_snd_5882_);
v___x_5890_ = lean_box(0);
v_isShared_5891_ = v_isSharedCheck_5948_;
goto v_resetjp_5889_;
}
v_resetjp_5889_:
{
lean_object* v_array_5892_; lean_object* v_start_5893_; lean_object* v_stop_5894_; uint8_t v___x_5895_; 
v_array_5892_ = lean_ctor_get(v_snd_5883_, 0);
v_start_5893_ = lean_ctor_get(v_snd_5883_, 1);
v_stop_5894_ = lean_ctor_get(v_snd_5883_, 2);
v___x_5895_ = lean_nat_dec_lt(v_start_5893_, v_stop_5894_);
if (v___x_5895_ == 0)
{
lean_object* v___x_5897_; 
lean_dec(v_a_5879_);
if (v_isShared_5891_ == 0)
{
v___x_5897_ = v___x_5890_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_fst_5888_);
lean_ctor_set(v_reuseFailAlloc_5901_, 1, v_snd_5883_);
v___x_5897_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
lean_object* v___x_5899_; 
if (v_isShared_5887_ == 0)
{
lean_ctor_set(v___x_5886_, 1, v___x_5897_);
v___x_5899_ = v___x_5886_;
goto v_reusejp_5898_;
}
else
{
lean_object* v_reuseFailAlloc_5900_; 
v_reuseFailAlloc_5900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5900_, 0, v_fst_5884_);
lean_ctor_set(v_reuseFailAlloc_5900_, 1, v___x_5897_);
v___x_5899_ = v_reuseFailAlloc_5900_;
goto v_reusejp_5898_;
}
v_reusejp_5898_:
{
return v___x_5899_;
}
}
}
else
{
lean_object* v___x_5903_; uint8_t v_isShared_5904_; uint8_t v_isSharedCheck_5944_; 
lean_inc(v_stop_5894_);
lean_inc(v_start_5893_);
lean_inc_ref(v_array_5892_);
v_isSharedCheck_5944_ = !lean_is_exclusive(v_snd_5883_);
if (v_isSharedCheck_5944_ == 0)
{
lean_object* v_unused_5945_; lean_object* v_unused_5946_; lean_object* v_unused_5947_; 
v_unused_5945_ = lean_ctor_get(v_snd_5883_, 2);
lean_dec(v_unused_5945_);
v_unused_5946_ = lean_ctor_get(v_snd_5883_, 1);
lean_dec(v_unused_5946_);
v_unused_5947_ = lean_ctor_get(v_snd_5883_, 0);
lean_dec(v_unused_5947_);
v___x_5903_ = v_snd_5883_;
v_isShared_5904_ = v_isSharedCheck_5944_;
goto v_resetjp_5902_;
}
else
{
lean_dec(v_snd_5883_);
v___x_5903_ = lean_box(0);
v_isShared_5904_ = v_isSharedCheck_5944_;
goto v_resetjp_5902_;
}
v_resetjp_5902_:
{
lean_object* v_array_5905_; lean_object* v_start_5906_; lean_object* v_stop_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5912_; 
v_array_5905_ = lean_ctor_get(v_fst_5888_, 0);
v_start_5906_ = lean_ctor_get(v_fst_5888_, 1);
v_stop_5907_ = lean_ctor_get(v_fst_5888_, 2);
v___x_5908_ = lean_array_fget(v_array_5892_, v_start_5893_);
v___x_5909_ = lean_unsigned_to_nat(1u);
v___x_5910_ = lean_nat_add(v_start_5893_, v___x_5909_);
lean_dec(v_start_5893_);
if (v_isShared_5904_ == 0)
{
lean_ctor_set(v___x_5903_, 1, v___x_5910_);
v___x_5912_ = v___x_5903_;
goto v_reusejp_5911_;
}
else
{
lean_object* v_reuseFailAlloc_5943_; 
v_reuseFailAlloc_5943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5943_, 0, v_array_5892_);
lean_ctor_set(v_reuseFailAlloc_5943_, 1, v___x_5910_);
lean_ctor_set(v_reuseFailAlloc_5943_, 2, v_stop_5894_);
v___x_5912_ = v_reuseFailAlloc_5943_;
goto v_reusejp_5911_;
}
v_reusejp_5911_:
{
uint8_t v___x_5913_; 
v___x_5913_ = lean_nat_dec_lt(v_start_5906_, v_stop_5907_);
if (v___x_5913_ == 0)
{
lean_object* v___x_5915_; 
lean_dec(v___x_5908_);
lean_dec(v_a_5879_);
if (v_isShared_5891_ == 0)
{
lean_ctor_set(v___x_5890_, 1, v___x_5912_);
v___x_5915_ = v___x_5890_;
goto v_reusejp_5914_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_fst_5888_);
lean_ctor_set(v_reuseFailAlloc_5919_, 1, v___x_5912_);
v___x_5915_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5914_;
}
v_reusejp_5914_:
{
lean_object* v___x_5917_; 
if (v_isShared_5887_ == 0)
{
lean_ctor_set(v___x_5886_, 1, v___x_5915_);
v___x_5917_ = v___x_5886_;
goto v_reusejp_5916_;
}
else
{
lean_object* v_reuseFailAlloc_5918_; 
v_reuseFailAlloc_5918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5918_, 0, v_fst_5884_);
lean_ctor_set(v_reuseFailAlloc_5918_, 1, v___x_5915_);
v___x_5917_ = v_reuseFailAlloc_5918_;
goto v_reusejp_5916_;
}
v_reusejp_5916_:
{
return v___x_5917_;
}
}
}
else
{
lean_object* v___x_5921_; uint8_t v_isShared_5922_; uint8_t v_isSharedCheck_5939_; 
lean_inc(v_stop_5907_);
lean_inc(v_start_5906_);
lean_inc_ref(v_array_5905_);
v_isSharedCheck_5939_ = !lean_is_exclusive(v_fst_5888_);
if (v_isSharedCheck_5939_ == 0)
{
lean_object* v_unused_5940_; lean_object* v_unused_5941_; lean_object* v_unused_5942_; 
v_unused_5940_ = lean_ctor_get(v_fst_5888_, 2);
lean_dec(v_unused_5940_);
v_unused_5941_ = lean_ctor_get(v_fst_5888_, 1);
lean_dec(v_unused_5941_);
v_unused_5942_ = lean_ctor_get(v_fst_5888_, 0);
lean_dec(v_unused_5942_);
v___x_5921_ = v_fst_5888_;
v_isShared_5922_ = v_isSharedCheck_5939_;
goto v_resetjp_5920_;
}
else
{
lean_dec(v_fst_5888_);
v___x_5921_ = lean_box(0);
v_isShared_5922_ = v_isSharedCheck_5939_;
goto v_resetjp_5920_;
}
v_resetjp_5920_:
{
lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5926_; 
v___x_5923_ = lean_array_fget(v_array_5905_, v_start_5906_);
v___x_5924_ = lean_nat_add(v_start_5906_, v___x_5909_);
lean_dec(v_start_5906_);
if (v_isShared_5922_ == 0)
{
lean_ctor_set(v___x_5921_, 1, v___x_5924_);
v___x_5926_ = v___x_5921_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_5938_; 
v_reuseFailAlloc_5938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5938_, 0, v_array_5905_);
lean_ctor_set(v_reuseFailAlloc_5938_, 1, v___x_5924_);
lean_ctor_set(v_reuseFailAlloc_5938_, 2, v_stop_5907_);
v___x_5926_ = v_reuseFailAlloc_5938_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
size_t v_sz_5927_; size_t v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5931_; 
v_sz_5927_ = lean_array_size(v___x_5923_);
v___x_5928_ = ((size_t)0ULL);
v___x_5929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5908_, v___x_5923_, v_sz_5927_, v___x_5928_, v_fst_5884_);
lean_dec(v___x_5923_);
lean_dec(v___x_5908_);
if (v_isShared_5891_ == 0)
{
lean_ctor_set(v___x_5890_, 1, v___x_5912_);
lean_ctor_set(v___x_5890_, 0, v___x_5926_);
v___x_5931_ = v___x_5890_;
goto v_reusejp_5930_;
}
else
{
lean_object* v_reuseFailAlloc_5937_; 
v_reuseFailAlloc_5937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5937_, 0, v___x_5926_);
lean_ctor_set(v_reuseFailAlloc_5937_, 1, v___x_5912_);
v___x_5931_ = v_reuseFailAlloc_5937_;
goto v_reusejp_5930_;
}
v_reusejp_5930_:
{
lean_object* v___x_5933_; 
if (v_isShared_5887_ == 0)
{
lean_ctor_set(v___x_5886_, 1, v___x_5931_);
lean_ctor_set(v___x_5886_, 0, v___x_5929_);
v___x_5933_ = v___x_5886_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5936_; 
v_reuseFailAlloc_5936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5936_, 0, v___x_5929_);
lean_ctor_set(v_reuseFailAlloc_5936_, 1, v___x_5931_);
v___x_5933_ = v_reuseFailAlloc_5936_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
lean_object* v___x_5934_; 
v___x_5934_ = lean_nat_add(v_a_5879_, v___x_5909_);
lean_dec(v_a_5879_);
v_a_5879_ = v___x_5934_;
v_b_5880_ = v___x_5933_;
goto _start;
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_5952_, lean_object* v_a_5953_, lean_object* v_b_5954_){
_start:
{
lean_object* v_res_5955_; 
v_res_5955_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_5952_, v_a_5953_, v_b_5954_);
lean_dec(v_upperBound_5952_);
return v_res_5955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5956_, size_t v_sz_5957_, size_t v_i_5958_, lean_object* v_bs_5959_){
_start:
{
uint8_t v___x_5960_; 
v___x_5960_ = lean_usize_dec_lt(v_i_5958_, v_sz_5957_);
if (v___x_5960_ == 0)
{
return v_bs_5959_;
}
else
{
lean_object* v_v_5961_; lean_object* v___x_5962_; lean_object* v_bs_x27_5963_; lean_object* v___y_5965_; 
v_v_5961_ = lean_array_uget(v_bs_5959_, v_i_5958_);
v___x_5962_ = lean_unsigned_to_nat(0u);
v_bs_x27_5963_ = lean_array_uset(v_bs_5959_, v_i_5958_, v___x_5962_);
if (lean_obj_tag(v_v_5961_) == 0)
{
v___y_5965_ = v_v_5961_;
goto v___jp_5964_;
}
else
{
lean_object* v_val_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; 
v_val_5970_ = lean_ctor_get(v_v_5961_, 0);
lean_inc(v_val_5970_);
lean_dec_ref_known(v_v_5961_, 1);
v___x_5971_ = lean_box(0);
v___x_5972_ = lean_array_get_borrowed(v___x_5971_, v___x_5956_, v_val_5970_);
lean_dec(v_val_5970_);
lean_inc(v___x_5972_);
v___y_5965_ = v___x_5972_;
goto v___jp_5964_;
}
v___jp_5964_:
{
size_t v___x_5966_; size_t v___x_5967_; lean_object* v___x_5968_; 
v___x_5966_ = ((size_t)1ULL);
v___x_5967_ = lean_usize_add(v_i_5958_, v___x_5966_);
v___x_5968_ = lean_array_uset(v_bs_x27_5963_, v_i_5958_, v___y_5965_);
v_i_5958_ = v___x_5967_;
v_bs_5959_ = v___x_5968_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5973_, lean_object* v_sz_5974_, lean_object* v_i_5975_, lean_object* v_bs_5976_){
_start:
{
size_t v_sz_boxed_5977_; size_t v_i_boxed_5978_; lean_object* v_res_5979_; 
v_sz_boxed_5977_ = lean_unbox_usize(v_sz_5974_);
lean_dec(v_sz_5974_);
v_i_boxed_5978_ = lean_unbox_usize(v_i_5975_);
lean_dec(v_i_5975_);
v_res_5979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5973_, v_sz_boxed_5977_, v_i_boxed_5978_, v_bs_5976_);
lean_dec_ref(v___x_5973_);
return v_res_5979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5980_, size_t v_sz_5981_, size_t v_i_5982_, lean_object* v_bs_5983_){
_start:
{
uint8_t v___x_5984_; 
v___x_5984_ = lean_usize_dec_lt(v_i_5982_, v_sz_5981_);
if (v___x_5984_ == 0)
{
return v_bs_5983_;
}
else
{
lean_object* v_v_5985_; lean_object* v___x_5986_; lean_object* v_bs_x27_5987_; size_t v_sz_5988_; size_t v___x_5989_; lean_object* v___x_5990_; size_t v___x_5991_; size_t v___x_5992_; lean_object* v___x_5993_; 
v_v_5985_ = lean_array_uget(v_bs_5983_, v_i_5982_);
v___x_5986_ = lean_unsigned_to_nat(0u);
v_bs_x27_5987_ = lean_array_uset(v_bs_5983_, v_i_5982_, v___x_5986_);
v_sz_5988_ = lean_array_size(v_v_5985_);
v___x_5989_ = ((size_t)0ULL);
v___x_5990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5980_, v_sz_5988_, v___x_5989_, v_v_5985_);
v___x_5991_ = ((size_t)1ULL);
v___x_5992_ = lean_usize_add(v_i_5982_, v___x_5991_);
v___x_5993_ = lean_array_uset(v_bs_x27_5987_, v_i_5982_, v___x_5990_);
v_i_5982_ = v___x_5992_;
v_bs_5983_ = v___x_5993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5995_, lean_object* v_sz_5996_, lean_object* v_i_5997_, lean_object* v_bs_5998_){
_start:
{
size_t v_sz_boxed_5999_; size_t v_i_boxed_6000_; lean_object* v_res_6001_; 
v_sz_boxed_5999_ = lean_unbox_usize(v_sz_5996_);
lean_dec(v_sz_5996_);
v_i_boxed_6000_ = lean_unbox_usize(v_i_5997_);
lean_dec(v_i_5997_);
v_res_6001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5995_, v_sz_boxed_5999_, v_i_boxed_6000_, v_bs_5998_);
lean_dec_ref(v___x_5995_);
return v_res_6001_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; 
v___x_6003_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_6004_ = lean_unsigned_to_nat(2u);
v___x_6005_ = lean_unsigned_to_nat(457u);
v___x_6006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6007_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6008_ = l_mkPanicMessageWithDecl(v___x_6007_, v___x_6006_, v___x_6005_, v___x_6004_, v___x_6003_);
return v___x_6008_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; 
v___x_6010_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_6011_ = lean_unsigned_to_nat(2u);
v___x_6012_ = lean_unsigned_to_nat(458u);
v___x_6013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6014_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6015_ = l_mkPanicMessageWithDecl(v___x_6014_, v___x_6013_, v___x_6012_, v___x_6011_, v___x_6010_);
return v___x_6015_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; 
v___x_6017_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_6018_ = lean_unsigned_to_nat(2u);
v___x_6019_ = lean_unsigned_to_nat(456u);
v___x_6020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6021_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6022_ = l_mkPanicMessageWithDecl(v___x_6021_, v___x_6020_, v___x_6019_, v___x_6018_, v___x_6017_);
return v___x_6022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6023_, lean_object* v_xs_6024_, lean_object* v_toErase_6025_){
_start:
{
lean_object* v___x_6026_; lean_object* v___x_6027_; uint8_t v___x_6111_; 
v___x_6026_ = lean_unsigned_to_nat(0u);
v___x_6027_ = lean_array_get_size(v_xs_6024_);
v___x_6111_ = lean_nat_dec_lt(v___x_6026_, v___x_6027_);
if (v___x_6111_ == 0)
{
goto v___jp_6028_;
}
else
{
if (v___x_6111_ == 0)
{
goto v___jp_6028_;
}
else
{
size_t v___x_6112_; size_t v___x_6113_; uint8_t v___x_6114_; 
v___x_6112_ = ((size_t)0ULL);
v___x_6113_ = lean_usize_of_nat(v___x_6027_);
v___x_6114_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6024_, v___x_6112_, v___x_6113_);
if (v___x_6114_ == 0)
{
goto v___jp_6028_;
}
else
{
lean_object* v___x_6115_; lean_object* v___x_6116_; 
lean_dec_ref(v_toErase_6025_);
lean_dec_ref(v_xs_6024_);
lean_dec_ref(v_fixedParamPerms_6023_);
v___x_6115_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6116_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6115_);
return v___x_6116_;
}
}
}
v___jp_6028_:
{
lean_object* v_numFixed_6029_; lean_object* v_perms_6030_; lean_object* v_revDeps_6031_; uint8_t v___x_6032_; 
v_numFixed_6029_ = lean_ctor_get(v_fixedParamPerms_6023_, 0);
v_perms_6030_ = lean_ctor_get(v_fixedParamPerms_6023_, 1);
lean_inc_ref(v_perms_6030_);
v_revDeps_6031_ = lean_ctor_get(v_fixedParamPerms_6023_, 2);
lean_inc_ref(v_revDeps_6031_);
v___x_6032_ = lean_nat_dec_eq(v_numFixed_6029_, v___x_6027_);
if (v___x_6032_ == 0)
{
lean_object* v___x_6033_; lean_object* v___x_6034_; 
lean_dec_ref(v_revDeps_6031_);
lean_dec_ref(v_perms_6030_);
lean_dec_ref(v_toErase_6025_);
lean_dec_ref(v_xs_6024_);
lean_dec_ref(v_fixedParamPerms_6023_);
v___x_6033_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6034_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6033_);
return v___x_6034_;
}
else
{
lean_object* v___x_6035_; lean_object* v___x_6036_; uint8_t v_changed_6037_; 
v___x_6035_ = lean_array_get_size(v_toErase_6025_);
v___x_6036_ = lean_array_get_size(v_perms_6030_);
v_changed_6037_ = lean_nat_dec_eq(v___x_6035_, v___x_6036_);
if (v_changed_6037_ == 0)
{
lean_object* v___x_6038_; lean_object* v___x_6039_; 
lean_dec_ref(v_revDeps_6031_);
lean_dec_ref(v_perms_6030_);
lean_dec_ref(v_toErase_6025_);
lean_dec_ref(v_xs_6024_);
lean_dec_ref(v_fixedParamPerms_6023_);
v___x_6038_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6039_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6038_);
return v___x_6039_;
}
else
{
uint8_t v_changed_6040_; lean_object* v___x_6041_; lean_object* v_mask_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v_fst_6048_; lean_object* v___x_6050_; uint8_t v_isShared_6051_; uint8_t v_isSharedCheck_6109_; 
v_changed_6040_ = 0;
v___x_6041_ = lean_box(v_changed_6040_);
lean_inc(v_numFixed_6029_);
v_mask_6042_ = lean_mk_array(v_numFixed_6029_, v___x_6041_);
v___x_6043_ = l_Array_toSubarray___redArg(v_toErase_6025_, v___x_6026_, v___x_6035_);
lean_inc_ref(v_perms_6030_);
v___x_6044_ = l_Array_toSubarray___redArg(v_perms_6030_, v___x_6026_, v___x_6036_);
v___x_6045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6043_);
lean_ctor_set(v___x_6045_, 1, v___x_6044_);
v___x_6046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6046_, 0, v_mask_6042_);
lean_ctor_set(v___x_6046_, 1, v___x_6045_);
v___x_6047_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6035_, v___x_6026_, v___x_6046_);
v_fst_6048_ = lean_ctor_get(v___x_6047_, 0);
v_isSharedCheck_6109_ = !lean_is_exclusive(v___x_6047_);
if (v_isSharedCheck_6109_ == 0)
{
lean_object* v_unused_6110_; 
v_unused_6110_ = lean_ctor_get(v___x_6047_, 1);
lean_dec(v_unused_6110_);
v___x_6050_ = v___x_6047_;
v_isShared_6051_ = v_isSharedCheck_6109_;
goto v_resetjp_6049_;
}
else
{
lean_inc(v_fst_6048_);
lean_dec(v___x_6047_);
v___x_6050_ = lean_box(0);
v_isShared_6051_ = v_isSharedCheck_6109_;
goto v_resetjp_6049_;
}
v_resetjp_6049_:
{
lean_object* v___x_6052_; lean_object* v___x_6054_; 
v___x_6052_ = lean_box(v_changed_6037_);
if (v_isShared_6051_ == 0)
{
lean_ctor_set(v___x_6050_, 1, v___x_6052_);
v___x_6054_ = v___x_6050_;
goto v_reusejp_6053_;
}
else
{
lean_object* v_reuseFailAlloc_6108_; 
v_reuseFailAlloc_6108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6108_, 0, v_fst_6048_);
lean_ctor_set(v_reuseFailAlloc_6108_, 1, v___x_6052_);
v___x_6054_ = v_reuseFailAlloc_6108_;
goto v_reusejp_6053_;
}
v_reusejp_6053_:
{
lean_object* v___x_6055_; lean_object* v___x_6057_; uint8_t v_isShared_6058_; uint8_t v_isSharedCheck_6104_; 
v___x_6055_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6036_, v_perms_6030_, v_fixedParamPerms_6023_, v___x_6054_);
v_isSharedCheck_6104_ = !lean_is_exclusive(v_fixedParamPerms_6023_);
if (v_isSharedCheck_6104_ == 0)
{
lean_object* v_unused_6105_; lean_object* v_unused_6106_; lean_object* v_unused_6107_; 
v_unused_6105_ = lean_ctor_get(v_fixedParamPerms_6023_, 2);
lean_dec(v_unused_6105_);
v_unused_6106_ = lean_ctor_get(v_fixedParamPerms_6023_, 1);
lean_dec(v_unused_6106_);
v_unused_6107_ = lean_ctor_get(v_fixedParamPerms_6023_, 0);
lean_dec(v_unused_6107_);
v___x_6057_ = v_fixedParamPerms_6023_;
v_isShared_6058_ = v_isSharedCheck_6104_;
goto v_resetjp_6056_;
}
else
{
lean_dec(v_fixedParamPerms_6023_);
v___x_6057_ = lean_box(0);
v_isShared_6058_ = v_isSharedCheck_6104_;
goto v_resetjp_6056_;
}
v_resetjp_6056_:
{
lean_object* v_fst_6059_; lean_object* v___x_6061_; uint8_t v_isShared_6062_; uint8_t v_isSharedCheck_6102_; 
v_fst_6059_ = lean_ctor_get(v___x_6055_, 0);
v_isSharedCheck_6102_ = !lean_is_exclusive(v___x_6055_);
if (v_isSharedCheck_6102_ == 0)
{
lean_object* v_unused_6103_; 
v_unused_6103_ = lean_ctor_get(v___x_6055_, 1);
lean_dec(v_unused_6103_);
v___x_6061_ = v___x_6055_;
v_isShared_6062_ = v_isSharedCheck_6102_;
goto v_resetjp_6060_;
}
else
{
lean_inc(v_fst_6059_);
lean_dec(v___x_6055_);
v___x_6061_ = lean_box(0);
v_isShared_6062_ = v_isSharedCheck_6102_;
goto v_resetjp_6060_;
}
v_resetjp_6060_:
{
lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6068_; 
v___x_6063_ = lean_array_get_size(v_fst_6059_);
v___x_6064_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6065_ = l_Array_toSubarray___redArg(v_fst_6059_, v___x_6026_, v___x_6063_);
v___x_6066_ = l_Array_toSubarray___redArg(v_xs_6024_, v___x_6026_, v___x_6027_);
if (v_isShared_6062_ == 0)
{
lean_ctor_set(v___x_6061_, 1, v___x_6066_);
lean_ctor_set(v___x_6061_, 0, v___x_6065_);
v___x_6068_ = v___x_6061_;
goto v_reusejp_6067_;
}
else
{
lean_object* v_reuseFailAlloc_6101_; 
v_reuseFailAlloc_6101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6101_, 0, v___x_6065_);
lean_ctor_set(v_reuseFailAlloc_6101_, 1, v___x_6066_);
v___x_6068_ = v_reuseFailAlloc_6101_;
goto v_reusejp_6067_;
}
v_reusejp_6067_:
{
lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v_snd_6073_; lean_object* v_snd_6074_; lean_object* v_fst_6075_; lean_object* v_fst_6076_; lean_object* v___x_6078_; uint8_t v_isShared_6079_; uint8_t v_isSharedCheck_6099_; 
v___x_6069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6064_);
lean_ctor_set(v___x_6069_, 1, v___x_6068_);
v___x_6070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6064_);
lean_ctor_set(v___x_6070_, 1, v___x_6069_);
v___x_6071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6064_);
lean_ctor_set(v___x_6071_, 1, v___x_6070_);
v___x_6072_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6063_, v___x_6026_, v___x_6071_);
v_snd_6073_ = lean_ctor_get(v___x_6072_, 1);
lean_inc(v_snd_6073_);
v_snd_6074_ = lean_ctor_get(v_snd_6073_, 1);
lean_inc(v_snd_6074_);
v_fst_6075_ = lean_ctor_get(v___x_6072_, 0);
lean_inc(v_fst_6075_);
lean_dec_ref(v___x_6072_);
v_fst_6076_ = lean_ctor_get(v_snd_6073_, 0);
v_isSharedCheck_6099_ = !lean_is_exclusive(v_snd_6073_);
if (v_isSharedCheck_6099_ == 0)
{
lean_object* v_unused_6100_; 
v_unused_6100_ = lean_ctor_get(v_snd_6073_, 1);
lean_dec(v_unused_6100_);
v___x_6078_ = v_snd_6073_;
v_isShared_6079_ = v_isSharedCheck_6099_;
goto v_resetjp_6077_;
}
else
{
lean_inc(v_fst_6076_);
lean_dec(v_snd_6073_);
v___x_6078_ = lean_box(0);
v_isShared_6079_ = v_isSharedCheck_6099_;
goto v_resetjp_6077_;
}
v_resetjp_6077_:
{
lean_object* v_fst_6080_; lean_object* v___x_6082_; uint8_t v_isShared_6083_; uint8_t v_isSharedCheck_6097_; 
v_fst_6080_ = lean_ctor_get(v_snd_6074_, 0);
v_isSharedCheck_6097_ = !lean_is_exclusive(v_snd_6074_);
if (v_isSharedCheck_6097_ == 0)
{
lean_object* v_unused_6098_; 
v_unused_6098_ = lean_ctor_get(v_snd_6074_, 1);
lean_dec(v_unused_6098_);
v___x_6082_ = v_snd_6074_;
v_isShared_6083_ = v_isSharedCheck_6097_;
goto v_resetjp_6081_;
}
else
{
lean_inc(v_fst_6080_);
lean_dec(v_snd_6074_);
v___x_6082_ = lean_box(0);
v_isShared_6083_ = v_isSharedCheck_6097_;
goto v_resetjp_6081_;
}
v_resetjp_6081_:
{
lean_object* v___x_6084_; size_t v_sz_6085_; size_t v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6089_; 
v___x_6084_ = lean_array_get_size(v_fst_6080_);
v_sz_6085_ = lean_array_size(v_perms_6030_);
v___x_6086_ = ((size_t)0ULL);
v___x_6087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6075_, v_sz_6085_, v___x_6086_, v_perms_6030_);
lean_dec(v_fst_6075_);
if (v_isShared_6058_ == 0)
{
lean_ctor_set(v___x_6057_, 1, v___x_6087_);
lean_ctor_set(v___x_6057_, 0, v___x_6084_);
v___x_6089_ = v___x_6057_;
goto v_reusejp_6088_;
}
else
{
lean_object* v_reuseFailAlloc_6096_; 
v_reuseFailAlloc_6096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6096_, 0, v___x_6084_);
lean_ctor_set(v_reuseFailAlloc_6096_, 1, v___x_6087_);
lean_ctor_set(v_reuseFailAlloc_6096_, 2, v_revDeps_6031_);
v___x_6089_ = v_reuseFailAlloc_6096_;
goto v_reusejp_6088_;
}
v_reusejp_6088_:
{
lean_object* v___x_6091_; 
if (v_isShared_6083_ == 0)
{
lean_ctor_set(v___x_6082_, 1, v_fst_6076_);
v___x_6091_ = v___x_6082_;
goto v_reusejp_6090_;
}
else
{
lean_object* v_reuseFailAlloc_6095_; 
v_reuseFailAlloc_6095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6095_, 0, v_fst_6080_);
lean_ctor_set(v_reuseFailAlloc_6095_, 1, v_fst_6076_);
v___x_6091_ = v_reuseFailAlloc_6095_;
goto v_reusejp_6090_;
}
v_reusejp_6090_:
{
lean_object* v___x_6093_; 
if (v_isShared_6079_ == 0)
{
lean_ctor_set(v___x_6078_, 1, v___x_6091_);
lean_ctor_set(v___x_6078_, 0, v___x_6089_);
v___x_6093_ = v___x_6078_;
goto v_reusejp_6092_;
}
else
{
lean_object* v_reuseFailAlloc_6094_; 
v_reuseFailAlloc_6094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6094_, 0, v___x_6089_);
lean_ctor_set(v_reuseFailAlloc_6094_, 1, v___x_6091_);
v___x_6093_ = v_reuseFailAlloc_6094_;
goto v_reusejp_6092_;
}
v_reusejp_6092_:
{
return v___x_6093_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6117_, lean_object* v___x_6118_, lean_object* v_fixedParamPerms_6119_, lean_object* v_next_6120_, lean_object* v_inst_6121_, lean_object* v_R_6122_, lean_object* v_a_6123_, lean_object* v_b_6124_, lean_object* v_c_6125_){
_start:
{
lean_object* v___x_6126_; 
v___x_6126_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6117_, v___x_6118_, v_fixedParamPerms_6119_, v_next_6120_, v_a_6123_, v_b_6124_);
return v___x_6126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6127_, lean_object* v___x_6128_, lean_object* v_fixedParamPerms_6129_, lean_object* v_next_6130_, lean_object* v_inst_6131_, lean_object* v_R_6132_, lean_object* v_a_6133_, lean_object* v_b_6134_, lean_object* v_c_6135_){
_start:
{
lean_object* v_res_6136_; 
v_res_6136_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6127_, v___x_6128_, v_fixedParamPerms_6129_, v_next_6130_, v_inst_6131_, v_R_6132_, v_a_6133_, v_b_6134_, v_c_6135_);
lean_dec(v_next_6130_);
lean_dec_ref(v_fixedParamPerms_6129_);
lean_dec_ref(v___x_6128_);
lean_dec(v_upperBound_6127_);
return v_res_6136_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6137_, lean_object* v___x_6138_, lean_object* v_fixedParamPerms_6139_, lean_object* v_inst_6140_, lean_object* v_R_6141_, lean_object* v_a_6142_, lean_object* v_b_6143_, lean_object* v_c_6144_){
_start:
{
lean_object* v___x_6145_; 
v___x_6145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6137_, v___x_6138_, v_fixedParamPerms_6139_, v_a_6142_, v_b_6143_);
return v___x_6145_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6146_, lean_object* v___x_6147_, lean_object* v_fixedParamPerms_6148_, lean_object* v_inst_6149_, lean_object* v_R_6150_, lean_object* v_a_6151_, lean_object* v_b_6152_, lean_object* v_c_6153_){
_start:
{
lean_object* v_res_6154_; 
v_res_6154_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6146_, v___x_6147_, v_fixedParamPerms_6148_, v_inst_6149_, v_R_6150_, v_a_6151_, v_b_6152_, v_c_6153_);
lean_dec_ref(v_fixedParamPerms_6148_);
lean_dec_ref(v___x_6147_);
lean_dec(v_upperBound_6146_);
return v_res_6154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6155_, lean_object* v___x_6156_, lean_object* v_fixedParamPerms_6157_, lean_object* v_inst_6158_, lean_object* v_a_6159_){
_start:
{
lean_object* v___x_6160_; 
v___x_6160_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6155_, v___x_6156_, v_fixedParamPerms_6157_, v_a_6159_);
return v___x_6160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6161_, lean_object* v___x_6162_, lean_object* v_fixedParamPerms_6163_, lean_object* v_inst_6164_, lean_object* v_a_6165_){
_start:
{
lean_object* v_res_6166_; 
v_res_6166_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6161_, v___x_6162_, v_fixedParamPerms_6163_, v_inst_6164_, v_a_6165_);
lean_dec_ref(v_fixedParamPerms_6163_);
lean_dec_ref(v___x_6162_);
lean_dec(v___x_6161_);
return v_res_6166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6167_, lean_object* v_inst_6168_, lean_object* v_R_6169_, lean_object* v_a_6170_, lean_object* v_b_6171_, lean_object* v_c_6172_){
_start:
{
lean_object* v___x_6173_; 
v___x_6173_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6167_, v_a_6170_, v_b_6171_);
return v___x_6173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6174_, lean_object* v_inst_6175_, lean_object* v_R_6176_, lean_object* v_a_6177_, lean_object* v_b_6178_, lean_object* v_c_6179_){
_start:
{
lean_object* v_res_6180_; 
v_res_6180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6174_, v_inst_6175_, v_R_6176_, v_a_6177_, v_b_6178_, v_c_6179_);
lean_dec(v_upperBound_6174_);
return v_res_6180_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6181_, lean_object* v_inst_6182_, lean_object* v_R_6183_, lean_object* v_a_6184_, lean_object* v_b_6185_, lean_object* v_c_6186_){
_start:
{
lean_object* v___x_6187_; 
v___x_6187_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6181_, v_a_6184_, v_b_6185_);
return v___x_6187_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6188_, lean_object* v_inst_6189_, lean_object* v_R_6190_, lean_object* v_a_6191_, lean_object* v_b_6192_, lean_object* v_c_6193_){
_start:
{
lean_object* v_res_6194_; 
v_res_6194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6188_, v_inst_6189_, v_R_6190_, v_a_6191_, v_b_6192_, v_c_6193_);
lean_dec(v_upperBound_6188_);
return v_res_6194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6252_; uint8_t v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6252_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6253_ = 0;
v___x_6254_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6255_ = l_Lean_registerTraceClass(v___x_6252_, v___x_6253_, v___x_6254_);
return v___x_6255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6256_){
_start:
{
lean_object* v_res_6257_; 
v_res_6257_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6257_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_PreDefinition_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
}
#ifdef __cplusplus
}
#endif
