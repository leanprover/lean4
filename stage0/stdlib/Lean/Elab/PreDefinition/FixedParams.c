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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_range(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Std_Format_indentD(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_init(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_addSelfCalls(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26_spec__27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__16(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fixedParams"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(80, 131, 105, 217, 25, 82, 145, 102)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__5_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "getFixedParams: notFixed "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__7_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ":\nIn "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "\ntoo few arguments for "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__13;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__14_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =/= "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__17;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " not matched"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__19;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Elab.PreDefinition.FixedParams"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Elab.getFixedParamsInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 185, .m_capacity = 185, .m_length = 184, .m_data = "assertion violation: params.size = arities[callerIdx]!\n\n      -- TODO: transform is overkill, a simple visit-all-subexpression that takes applications\n      -- as whole suffices\n      "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_getFixedParamsInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "getFixedParams:"};
static const lean_object* l_Lean_Elab_getFixedParamsInfo___closed__0 = (const lean_object*)&l_Lean_Elab_getFixedParamsInfo___closed__0_value;
static lean_once_cell_t l_Lean_Elab_getFixedParamsInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getFixedParamsInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__26(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26_spec__27(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Elab.getFixedParamPerms"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "assertion violation: firstPerm[firstParamIdx]!.isSome\n            "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Incomplete paramInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "assertion violation: paramInfo[0]! = some paramIdx\n        "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "_private.Lean.Elab.PreDefinition.FixedParams.0.Lean.Elab.FixedParamPerm.instantiateLambda.go"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "assertion violation: ys.size = 1\n            "};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 144, 90, 0, 164, 70, 155, 205)}};
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(lean_object* v_i_31_, lean_object* v_as_32_, lean_object* v_i_33_, lean_object* v_j_34_, lean_object* v_bs_35_){
_start:
{
lean_object* v_zero_36_; uint8_t v_isZero_37_; 
v_zero_36_ = lean_unsigned_to_nat(0u);
v_isZero_37_ = lean_nat_dec_eq(v_i_33_, v_zero_36_);
if (v_isZero_37_ == 1)
{
lean_dec(v_j_34_);
lean_dec(v_i_33_);
return v_bs_35_;
}
else
{
lean_object* v_one_38_; lean_object* v_n_39_; lean_object* v___y_41_; lean_object* v___x_45_; 
v_one_38_ = lean_unsigned_to_nat(1u);
v_n_39_ = lean_nat_sub(v_i_33_, v_one_38_);
lean_dec(v_i_33_);
v___x_45_ = lean_array_fget(v_as_32_, v_j_34_);
if (lean_obj_tag(v___x_45_) == 0)
{
v___y_41_ = v___x_45_;
goto v___jp_40_;
}
else
{
lean_object* v_val_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_55_; 
v_val_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_55_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_55_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_val_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_55_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
lean_inc(v_j_34_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v_j_34_);
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_j_34_);
v___x_51_ = v_reuseFailAlloc_54_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_array_set(v_val_46_, v_i_31_, v___x_51_);
v___x_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
v___y_41_ = v___x_53_;
goto v___jp_40_;
}
}
}
v___jp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_nat_add(v_j_34_, v_one_38_);
lean_dec(v_j_34_);
v___x_43_ = lean_array_push(v_bs_35_, v___y_41_);
v_i_33_ = v_n_39_;
v_j_34_ = v___x_42_;
v_bs_35_ = v___x_43_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg___boxed(lean_object* v_i_56_, lean_object* v_as_57_, lean_object* v_i_58_, lean_object* v_j_59_, lean_object* v_bs_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(v_i_56_, v_as_57_, v_i_58_, v_j_59_, v_bs_60_);
lean_dec_ref(v_as_57_);
lean_dec(v_i_56_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(lean_object* v_as_62_, lean_object* v_i_63_, lean_object* v_j_64_, lean_object* v_bs_65_){
_start:
{
lean_object* v_zero_66_; uint8_t v_isZero_67_; 
v_zero_66_ = lean_unsigned_to_nat(0u);
v_isZero_67_ = lean_nat_dec_eq(v_i_63_, v_zero_66_);
if (v_isZero_67_ == 1)
{
lean_dec(v_j_64_);
lean_dec(v_i_63_);
return v_bs_65_;
}
else
{
lean_object* v_one_68_; lean_object* v_n_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_one_68_ = lean_unsigned_to_nat(1u);
v_n_69_ = lean_nat_sub(v_i_63_, v_one_68_);
lean_dec(v_i_63_);
v___x_70_ = lean_array_fget_borrowed(v_as_62_, v_j_64_);
v___x_71_ = lean_array_get_size(v___x_70_);
v___x_72_ = lean_mk_empty_array_with_capacity(v___x_71_);
v___x_73_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(v_j_64_, v___x_70_, v___x_71_, v_zero_66_, v___x_72_);
v___x_74_ = lean_nat_add(v_j_64_, v_one_68_);
lean_dec(v_j_64_);
v___x_75_ = lean_array_push(v_bs_65_, v___x_73_);
v_i_63_ = v_n_69_;
v_j_64_ = v___x_74_;
v_bs_65_ = v___x_75_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg___boxed(lean_object* v_as_77_, lean_object* v_i_78_, lean_object* v_j_79_, lean_object* v_bs_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(v_as_77_, v_i_78_, v_j_79_, v_bs_80_);
lean_dec_ref(v_as_77_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_addSelfCalls(lean_object* v_info_82_){
_start:
{
lean_object* v_graph_83_; lean_object* v_revDeps_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_95_; 
v_graph_83_ = lean_ctor_get(v_info_82_, 0);
v_revDeps_84_ = lean_ctor_get(v_info_82_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v_info_82_);
if (v_isSharedCheck_95_ == 0)
{
v___x_86_ = v_info_82_;
v_isShared_87_ = v_isSharedCheck_95_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_revDeps_84_);
lean_inc(v_graph_83_);
lean_dec(v_info_82_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_95_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_88_ = lean_array_get_size(v_graph_83_);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_mk_empty_array_with_capacity(v___x_88_);
v___x_91_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(v_graph_83_, v___x_88_, v___x_89_, v___x_90_);
lean_dec_ref(v_graph_83_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_91_);
v___x_93_ = v___x_86_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_revDeps_84_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0(lean_object* v_i_96_, lean_object* v_as_97_, lean_object* v_i_98_, lean_object* v_j_99_, lean_object* v_inv_100_, lean_object* v_bs_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(v_i_96_, v_as_97_, v_i_98_, v_j_99_, v_bs_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___boxed(lean_object* v_i_103_, lean_object* v_as_104_, lean_object* v_i_105_, lean_object* v_j_106_, lean_object* v_inv_107_, lean_object* v_bs_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0(v_i_103_, v_as_104_, v_i_105_, v_j_106_, v_inv_107_, v_bs_108_);
lean_dec_ref(v_as_104_);
lean_dec(v_i_103_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1(lean_object* v_as_110_, lean_object* v_i_111_, lean_object* v_j_112_, lean_object* v_inv_113_, lean_object* v_bs_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(v_as_110_, v_i_111_, v_j_112_, v_bs_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___boxed(lean_object* v_as_116_, lean_object* v_i_117_, lean_object* v_j_118_, lean_object* v_inv_119_, lean_object* v_bs_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1(v_as_116_, v_i_117_, v_j_118_, v_inv_119_, v_bs_120_);
lean_dec_ref(v_as_116_);
return v_res_121_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Array_instInhabited(lean_box(0));
return v___x_122_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParams_Info_mayBeFixed(lean_object* v_callerIdx_123_, lean_object* v_paramIdx_124_, lean_object* v_info_125_){
_start:
{
lean_object* v_graph_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_graph_126_ = lean_ctor_get(v_info_125_, 0);
v___x_127_ = lean_box(0);
v___x_128_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_129_ = lean_array_get_borrowed(v___x_128_, v_graph_126_, v_callerIdx_123_);
v___x_130_ = lean_array_get_borrowed(v___x_127_, v___x_129_, v_paramIdx_124_);
if (lean_obj_tag(v___x_130_) == 0)
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 1;
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_mayBeFixed___boxed(lean_object* v_callerIdx_133_, lean_object* v_paramIdx_134_, lean_object* v_info_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_callerIdx_133_, v_paramIdx_134_, v_info_135_);
lean_dec_ref(v_info_135_);
lean_dec(v_paramIdx_134_);
lean_dec(v_callerIdx_133_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(lean_object* v_upperBound_138_, lean_object* v_next_139_, lean_object* v_funIdx_140_, lean_object* v_paramIdx_141_, lean_object* v_a_142_, lean_object* v_b_143_){
_start:
{
lean_object* v_a_145_; uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_lt(v_a_142_, v_upperBound_138_);
if (v___x_149_ == 0)
{
lean_dec(v_a_142_);
lean_dec(v_paramIdx_141_);
return v_b_143_;
}
else
{
lean_object* v_graph_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_graph_150_ = lean_ctor_get(v_b_143_, 0);
v___x_151_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_152_ = lean_box(0);
v___x_153_ = lean_array_get_borrowed(v___x_151_, v_graph_150_, v_next_139_);
v___x_154_ = lean_array_get(v___x_152_, v___x_153_, v_a_142_);
if (lean_obj_tag(v___x_154_) == 1)
{
lean_object* v_val_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_166_; 
v_val_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_166_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_166_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_val_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_166_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_159_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_160_ = lean_array_get(v___x_152_, v_val_155_, v_funIdx_140_);
lean_dec(v_val_155_);
lean_inc(v_paramIdx_141_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v_paramIdx_141_);
v___x_162_ = v___x_157_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_paramIdx_141_);
v___x_162_ = v_reuseFailAlloc_165_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
uint8_t v___x_163_; 
v___x_163_ = l_Option_instDecidableEq___redArg(v___x_159_, v___x_160_, v___x_162_);
if (v___x_163_ == 0)
{
v_a_145_ = v_b_143_;
goto v___jp_144_;
}
else
{
lean_object* v___x_164_; 
lean_inc(v_a_142_);
v___x_164_ = l_Lean_Elab_FixedParams_Info_setVarying(v_next_139_, v_a_142_, v_b_143_);
v_a_145_ = v___x_164_;
goto v___jp_144_;
}
}
}
}
else
{
lean_dec(v___x_154_);
v_a_145_ = v_b_143_;
goto v___jp_144_;
}
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_add(v_a_142_, v___x_146_);
lean_dec(v_a_142_);
v_a_142_ = v___x_147_;
v_b_143_ = v_a_145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(lean_object* v_upperBound_167_, lean_object* v_funIdx_168_, lean_object* v_paramIdx_169_, lean_object* v_a_170_, lean_object* v_b_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = lean_nat_dec_lt(v_a_170_, v_upperBound_167_);
if (v___x_172_ == 0)
{
lean_dec(v_a_170_);
lean_dec(v_paramIdx_169_);
return v_b_171_;
}
else
{
lean_object* v_graph_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_graph_173_ = lean_ctor_get(v_b_171_, 0);
v___x_174_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_175_ = lean_array_get_borrowed(v___x_174_, v_graph_173_, v_a_170_);
v___x_176_ = lean_array_get_size(v___x_175_);
v___x_177_ = lean_unsigned_to_nat(0u);
lean_inc(v_paramIdx_169_);
v___x_178_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(v___x_176_, v_a_170_, v_funIdx_168_, v_paramIdx_169_, v___x_177_, v_b_171_);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_add(v_a_170_, v___x_179_);
lean_dec(v_a_170_);
v_a_170_ = v___x_180_;
v_b_171_ = v___x_178_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0(void){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Array_instInhabited(lean_box(0));
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setVarying(lean_object* v_funIdx_183_, lean_object* v_paramIdx_184_, lean_object* v_info_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_funIdx_183_, v_paramIdx_184_, v_info_185_);
if (v___x_186_ == 0)
{
lean_dec(v_paramIdx_184_);
return v_info_185_;
}
else
{
lean_object* v_graph_187_; lean_object* v_revDeps_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_215_; 
v_graph_187_ = lean_ctor_get(v_info_185_, 0);
v_revDeps_188_ = lean_ctor_get(v_info_185_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_info_185_);
if (v_isSharedCheck_215_ == 0)
{
v___x_190_ = v_info_185_;
v_isShared_191_ = v_isSharedCheck_215_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_revDeps_188_);
lean_inc(v_graph_187_);
lean_dec(v_info_185_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_215_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___y_193_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_array_get_size(v_graph_187_);
v___x_208_ = lean_nat_dec_lt(v_funIdx_183_, v___x_207_);
if (v___x_208_ == 0)
{
v___y_193_ = v_graph_187_;
goto v___jp_192_;
}
else
{
lean_object* v_v_209_; lean_object* v___x_210_; lean_object* v_xs_x27_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_v_209_ = lean_array_fget(v_graph_187_, v_funIdx_183_);
v___x_210_ = lean_box(0);
v_xs_x27_211_ = lean_array_fset(v_graph_187_, v_funIdx_183_, v___x_210_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_array_set(v_v_209_, v_paramIdx_184_, v___x_212_);
v___x_214_ = lean_array_fset(v_xs_x27_211_, v_funIdx_183_, v___x_213_);
v___y_193_ = v___x_214_;
goto v___jp_192_;
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_info_197_; 
v___x_194_ = lean_array_get_size(v___y_193_);
v___x_195_ = lean_unsigned_to_nat(0u);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___y_193_);
v_info_197_ = v___x_190_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___y_193_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_revDeps_188_);
v_info_197_ = v_reuseFailAlloc_206_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v_revDeps_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; size_t v_sz_203_; size_t v___x_204_; lean_object* v___x_205_; 
lean_inc(v_paramIdx_184_);
v___x_198_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(v___x_194_, v_funIdx_183_, v_paramIdx_184_, v___x_195_, v_info_197_);
v_revDeps_199_ = lean_ctor_get(v___x_198_, 1);
lean_inc_ref(v_revDeps_199_);
v___x_200_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_201_ = lean_array_get(v___x_200_, v_revDeps_199_, v_funIdx_183_);
lean_dec_ref(v_revDeps_199_);
v___x_202_ = lean_array_get(v___x_200_, v___x_201_, v_paramIdx_184_);
lean_dec(v_paramIdx_184_);
lean_dec(v___x_201_);
v_sz_203_ = lean_array_size(v___x_202_);
v___x_204_ = ((size_t)0ULL);
v___x_205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(v_funIdx_183_, v___x_202_, v_sz_203_, v___x_204_, v___x_198_);
lean_dec(v___x_202_);
return v___x_205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(lean_object* v_funIdx_216_, lean_object* v_as_217_, size_t v_sz_218_, size_t v_i_219_, lean_object* v_b_220_){
_start:
{
uint8_t v___x_221_; 
v___x_221_ = lean_usize_dec_lt(v_i_219_, v_sz_218_);
if (v___x_221_ == 0)
{
return v_b_220_;
}
else
{
lean_object* v_a_222_; lean_object* v___x_223_; size_t v___x_224_; size_t v___x_225_; 
v_a_222_ = lean_array_uget_borrowed(v_as_217_, v_i_219_);
lean_inc(v_a_222_);
v___x_223_ = l_Lean_Elab_FixedParams_Info_setVarying(v_funIdx_216_, v_a_222_, v_b_220_);
v___x_224_ = ((size_t)1ULL);
v___x_225_ = lean_usize_add(v_i_219_, v___x_224_);
v_i_219_ = v___x_225_;
v_b_220_ = v___x_223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0___boxed(lean_object* v_funIdx_227_, lean_object* v_as_228_, lean_object* v_sz_229_, lean_object* v_i_230_, lean_object* v_b_231_){
_start:
{
size_t v_sz_boxed_232_; size_t v_i_boxed_233_; lean_object* v_res_234_; 
v_sz_boxed_232_ = lean_unbox_usize(v_sz_229_);
lean_dec(v_sz_229_);
v_i_boxed_233_ = lean_unbox_usize(v_i_230_);
lean_dec(v_i_230_);
v_res_234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(v_funIdx_227_, v_as_228_, v_sz_boxed_232_, v_i_boxed_233_, v_b_231_);
lean_dec_ref(v_as_228_);
lean_dec(v_funIdx_227_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg___boxed(lean_object* v_upperBound_235_, lean_object* v_funIdx_236_, lean_object* v_paramIdx_237_, lean_object* v_a_238_, lean_object* v_b_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(v_upperBound_235_, v_funIdx_236_, v_paramIdx_237_, v_a_238_, v_b_239_);
lean_dec(v_funIdx_236_);
lean_dec(v_upperBound_235_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg___boxed(lean_object* v_upperBound_241_, lean_object* v_next_242_, lean_object* v_funIdx_243_, lean_object* v_paramIdx_244_, lean_object* v_a_245_, lean_object* v_b_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(v_upperBound_241_, v_next_242_, v_funIdx_243_, v_paramIdx_244_, v_a_245_, v_b_246_);
lean_dec(v_funIdx_243_);
lean_dec(v_next_242_);
lean_dec(v_upperBound_241_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setVarying___boxed(lean_object* v_funIdx_248_, lean_object* v_paramIdx_249_, lean_object* v_info_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Elab_FixedParams_Info_setVarying(v_funIdx_248_, v_paramIdx_249_, v_info_250_);
lean_dec(v_funIdx_248_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1(lean_object* v_upperBound_252_, lean_object* v_next_253_, lean_object* v_funIdx_254_, lean_object* v_paramIdx_255_, lean_object* v_inst_256_, lean_object* v_R_257_, lean_object* v_a_258_, lean_object* v_b_259_, lean_object* v_c_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(v_upperBound_252_, v_next_253_, v_funIdx_254_, v_paramIdx_255_, v_a_258_, v_b_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___boxed(lean_object* v_upperBound_262_, lean_object* v_next_263_, lean_object* v_funIdx_264_, lean_object* v_paramIdx_265_, lean_object* v_inst_266_, lean_object* v_R_267_, lean_object* v_a_268_, lean_object* v_b_269_, lean_object* v_c_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1(v_upperBound_262_, v_next_263_, v_funIdx_264_, v_paramIdx_265_, v_inst_266_, v_R_267_, v_a_268_, v_b_269_, v_c_270_);
lean_dec(v_funIdx_264_);
lean_dec(v_next_263_);
lean_dec(v_upperBound_262_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2(lean_object* v_upperBound_272_, lean_object* v_funIdx_273_, lean_object* v_paramIdx_274_, lean_object* v_inst_275_, lean_object* v_R_276_, lean_object* v_a_277_, lean_object* v_b_278_, lean_object* v_c_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(v_upperBound_272_, v_funIdx_273_, v_paramIdx_274_, v_a_277_, v_b_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___boxed(lean_object* v_upperBound_281_, lean_object* v_funIdx_282_, lean_object* v_paramIdx_283_, lean_object* v_inst_284_, lean_object* v_R_285_, lean_object* v_a_286_, lean_object* v_b_287_, lean_object* v_c_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2(v_upperBound_281_, v_funIdx_282_, v_paramIdx_283_, v_inst_284_, v_R_285_, v_a_286_, v_b_287_, v_c_288_);
lean_dec(v_funIdx_282_);
lean_dec(v_upperBound_281_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(lean_object* v_calleeIdx_290_, lean_object* v_argIdx_291_, lean_object* v_callerIdx_292_, lean_object* v_info_293_){
_start:
{
lean_object* v_graph_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_graph_294_ = lean_ctor_get(v_info_293_, 0);
v___x_295_ = lean_box(0);
v___x_296_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_297_ = lean_array_get_borrowed(v___x_296_, v_graph_294_, v_calleeIdx_290_);
v___x_298_ = lean_array_get_borrowed(v___x_295_, v___x_297_, v_argIdx_291_);
if (lean_obj_tag(v___x_298_) == 0)
{
return v___x_295_;
}
else
{
lean_object* v_val_299_; lean_object* v___x_300_; 
v_val_299_ = lean_ctor_get(v___x_298_, 0);
v___x_300_ = lean_array_get_borrowed(v___x_295_, v_val_299_, v_callerIdx_292_);
lean_inc(v___x_300_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_getCallerParam_x3f___boxed(lean_object* v_calleeIdx_301_, lean_object* v_argIdx_302_, lean_object* v_callerIdx_303_, lean_object* v_info_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_calleeIdx_301_, v_argIdx_302_, v_callerIdx_303_, v_info_304_);
lean_dec_ref(v_info_304_);
lean_dec(v_callerIdx_303_);
lean_dec(v_argIdx_302_);
lean_dec(v_calleeIdx_301_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(lean_object* v_upperBound_306_, lean_object* v_val_307_, lean_object* v_calleeIdx_308_, lean_object* v_argIdx_309_, lean_object* v_a_310_, lean_object* v_b_311_){
_start:
{
lean_object* v_a_313_; uint8_t v___x_317_; 
v___x_317_ = lean_nat_dec_lt(v_a_310_, v_upperBound_306_);
if (v___x_317_ == 0)
{
lean_dec(v_a_310_);
lean_dec(v_argIdx_309_);
return v_b_311_;
}
else
{
lean_object* v___x_318_; 
v___x_318_ = lean_array_fget_borrowed(v_val_307_, v_a_310_);
if (lean_obj_tag(v___x_318_) == 1)
{
lean_object* v_val_319_; lean_object* v___x_320_; 
v_val_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_val_319_);
lean_inc(v_argIdx_309_);
v___x_320_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_calleeIdx_308_, v_argIdx_309_, v_a_310_, v_val_319_, v_b_311_);
v_a_313_ = v___x_320_;
goto v___jp_312_;
}
else
{
v_a_313_ = v_b_311_;
goto v___jp_312_;
}
}
v___jp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_nat_add(v_a_310_, v___x_314_);
lean_dec(v_a_310_);
v_a_310_ = v___x_315_;
v_b_311_ = v_a_313_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setCallerParam(lean_object* v_calleeIdx_321_, lean_object* v_argIdx_322_, lean_object* v_callerIdx_323_, lean_object* v_paramIdx_324_, lean_object* v_info_325_){
_start:
{
lean_object* v_info_327_; lean_object* v_graph_328_; uint8_t v___x_332_; 
v___x_332_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_calleeIdx_321_, v_argIdx_322_, v_info_325_);
if (v___x_332_ == 0)
{
lean_dec(v_paramIdx_324_);
lean_dec(v_argIdx_322_);
return v_info_325_;
}
else
{
uint8_t v___x_333_; 
v___x_333_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_callerIdx_323_, v_paramIdx_324_, v_info_325_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
lean_dec(v_paramIdx_324_);
v___x_334_ = l_Lean_Elab_FixedParams_Info_setVarying(v_calleeIdx_321_, v_argIdx_322_, v_info_325_);
return v___x_334_;
}
else
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_calleeIdx_321_, v_argIdx_322_, v_callerIdx_323_, v_info_325_);
if (lean_obj_tag(v___x_335_) == 1)
{
lean_object* v_val_336_; uint8_t v___x_337_; 
v_val_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_val_336_);
lean_dec_ref(v___x_335_);
v___x_337_ = lean_nat_dec_eq(v_paramIdx_324_, v_val_336_);
lean_dec(v_val_336_);
lean_dec(v_paramIdx_324_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Elab_FixedParams_Info_setVarying(v_calleeIdx_321_, v_argIdx_322_, v_info_325_);
return v___x_338_;
}
else
{
lean_dec(v_argIdx_322_);
return v_info_325_;
}
}
else
{
lean_object* v_graph_339_; lean_object* v_revDeps_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_383_; 
lean_dec(v___x_335_);
v_graph_339_ = lean_ctor_get(v_info_325_, 0);
v_revDeps_340_ = lean_ctor_get(v_info_325_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_info_325_);
if (v_isSharedCheck_383_ == 0)
{
v___x_342_ = v_info_325_;
v_isShared_343_ = v_isSharedCheck_383_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_revDeps_340_);
lean_inc(v_graph_339_);
lean_dec(v_info_325_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_383_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___y_345_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = lean_array_get_size(v_graph_339_);
v___x_359_ = lean_nat_dec_lt(v_calleeIdx_321_, v___x_358_);
if (v___x_359_ == 0)
{
v___y_345_ = v_graph_339_;
goto v___jp_344_;
}
else
{
lean_object* v_v_360_; lean_object* v___x_361_; lean_object* v_xs_x27_362_; lean_object* v___y_364_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_v_360_ = lean_array_fget(v_graph_339_, v_calleeIdx_321_);
v___x_361_ = lean_box(0);
v_xs_x27_362_ = lean_array_fset(v_graph_339_, v_calleeIdx_321_, v___x_361_);
v___x_366_ = lean_array_get_size(v_v_360_);
v___x_367_ = lean_nat_dec_lt(v_argIdx_322_, v___x_366_);
if (v___x_367_ == 0)
{
v___y_364_ = v_v_360_;
goto v___jp_363_;
}
else
{
lean_object* v_v_368_; lean_object* v_xs_x27_369_; lean_object* v___y_371_; 
v_v_368_ = lean_array_fget(v_v_360_, v_argIdx_322_);
v_xs_x27_369_ = lean_array_fset(v_v_360_, v_argIdx_322_, v___x_361_);
if (lean_obj_tag(v_v_368_) == 0)
{
v___y_371_ = v_v_368_;
goto v___jp_370_;
}
else
{
lean_object* v_val_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_382_; 
v_val_373_ = lean_ctor_get(v_v_368_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v_v_368_);
if (v_isSharedCheck_382_ == 0)
{
v___x_375_ = v_v_368_;
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_val_373_);
lean_dec(v_v_368_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
lean_inc(v_paramIdx_324_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v_paramIdx_324_);
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_paramIdx_324_);
v___x_378_ = v_reuseFailAlloc_381_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_array_set(v_val_373_, v_callerIdx_323_, v___x_378_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
v___y_371_ = v___x_380_;
goto v___jp_370_;
}
}
}
v___jp_370_:
{
lean_object* v___x_372_; 
v___x_372_ = lean_array_fset(v_xs_x27_369_, v_argIdx_322_, v___y_371_);
v___y_364_ = v___x_372_;
goto v___jp_363_;
}
}
v___jp_363_:
{
lean_object* v___x_365_; 
v___x_365_ = lean_array_fset(v_xs_x27_362_, v_calleeIdx_321_, v___y_364_);
v___y_345_ = v___x_365_;
goto v___jp_344_;
}
}
v___jp_344_:
{
lean_object* v_info_347_; 
lean_inc_ref(v___y_345_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___y_345_);
v_info_347_ = v___x_342_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___y_345_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_revDeps_340_);
v_info_347_ = v_reuseFailAlloc_357_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_348_ = lean_box(0);
v___x_349_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_350_ = lean_array_get_borrowed(v___x_349_, v___y_345_, v_callerIdx_323_);
v___x_351_ = lean_array_get_borrowed(v___x_348_, v___x_350_, v_paramIdx_324_);
if (lean_obj_tag(v___x_351_) == 1)
{
lean_object* v_val_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_graph_356_; 
lean_inc_ref(v___x_351_);
lean_dec_ref(v___y_345_);
v_val_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_val_352_);
lean_dec_ref(v___x_351_);
v___x_353_ = lean_array_get_size(v_val_352_);
v___x_354_ = lean_unsigned_to_nat(0u);
lean_inc(v_argIdx_322_);
v___x_355_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(v___x_353_, v_val_352_, v_calleeIdx_321_, v_argIdx_322_, v___x_354_, v_info_347_);
lean_dec(v_val_352_);
v_graph_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc_ref(v_graph_356_);
v_info_327_ = v___x_355_;
v_graph_328_ = v_graph_356_;
goto v___jp_326_;
}
else
{
v_info_327_ = v_info_347_;
v_graph_328_ = v___y_345_;
goto v___jp_326_;
}
}
}
}
}
}
}
v___jp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_array_get_size(v_graph_328_);
lean_dec_ref(v_graph_328_);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(v___x_329_, v_calleeIdx_321_, v_argIdx_322_, v_callerIdx_323_, v_paramIdx_324_, v___x_330_, v_info_327_);
lean_dec(v_argIdx_322_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(lean_object* v_upperBound_384_, lean_object* v_next_385_, lean_object* v_calleeIdx_386_, lean_object* v_argIdx_387_, lean_object* v_callerIdx_388_, lean_object* v_paramIdx_389_, lean_object* v_a_390_, lean_object* v_b_391_){
_start:
{
lean_object* v_a_393_; uint8_t v___x_397_; 
v___x_397_ = lean_nat_dec_lt(v_a_390_, v_upperBound_384_);
if (v___x_397_ == 0)
{
lean_dec(v_a_390_);
lean_dec(v_paramIdx_389_);
return v_b_391_;
}
else
{
lean_object* v_graph_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_graph_398_ = lean_ctor_get(v_b_391_, 0);
v___x_399_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_400_ = lean_box(0);
v___x_401_ = lean_array_get_borrowed(v___x_399_, v_graph_398_, v_next_385_);
v___x_402_ = lean_array_get_borrowed(v___x_400_, v___x_401_, v_a_390_);
if (lean_obj_tag(v___x_402_) == 1)
{
lean_object* v_val_403_; lean_object* v___x_404_; 
v_val_403_ = lean_ctor_get(v___x_402_, 0);
v___x_404_ = lean_array_get_borrowed(v___x_400_, v_val_403_, v_calleeIdx_386_);
if (lean_obj_tag(v___x_404_) == 1)
{
lean_object* v_val_405_; uint8_t v___x_406_; 
v_val_405_ = lean_ctor_get(v___x_404_, 0);
v___x_406_ = lean_nat_dec_eq(v_val_405_, v_argIdx_387_);
if (v___x_406_ == 0)
{
v_a_393_ = v_b_391_;
goto v___jp_392_;
}
else
{
lean_object* v___x_407_; 
lean_inc(v_paramIdx_389_);
lean_inc(v_a_390_);
v___x_407_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_next_385_, v_a_390_, v_callerIdx_388_, v_paramIdx_389_, v_b_391_);
v_a_393_ = v___x_407_;
goto v___jp_392_;
}
}
else
{
v_a_393_ = v_b_391_;
goto v___jp_392_;
}
}
else
{
v_a_393_ = v_b_391_;
goto v___jp_392_;
}
}
v___jp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_a_390_, v___x_394_);
lean_dec(v_a_390_);
v_a_390_ = v___x_395_;
v_b_391_ = v_a_393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(lean_object* v_upperBound_408_, lean_object* v_calleeIdx_409_, lean_object* v_argIdx_410_, lean_object* v_callerIdx_411_, lean_object* v_paramIdx_412_, lean_object* v_a_413_, lean_object* v_b_414_){
_start:
{
uint8_t v___x_415_; 
v___x_415_ = lean_nat_dec_lt(v_a_413_, v_upperBound_408_);
if (v___x_415_ == 0)
{
lean_dec(v_a_413_);
lean_dec(v_paramIdx_412_);
return v_b_414_;
}
else
{
lean_object* v_graph_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_graph_416_ = lean_ctor_get(v_b_414_, 0);
v___x_417_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_418_ = lean_array_get_borrowed(v___x_417_, v_graph_416_, v_a_413_);
v___x_419_ = lean_array_get_size(v___x_418_);
v___x_420_ = lean_unsigned_to_nat(0u);
lean_inc(v_paramIdx_412_);
v___x_421_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(v___x_419_, v_a_413_, v_calleeIdx_409_, v_argIdx_410_, v_callerIdx_411_, v_paramIdx_412_, v___x_420_, v_b_414_);
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_a_413_, v___x_422_);
lean_dec(v_a_413_);
v_a_413_ = v___x_423_;
v_b_414_ = v___x_421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg___boxed(lean_object* v_upperBound_425_, lean_object* v_calleeIdx_426_, lean_object* v_argIdx_427_, lean_object* v_callerIdx_428_, lean_object* v_paramIdx_429_, lean_object* v_a_430_, lean_object* v_b_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(v_upperBound_425_, v_calleeIdx_426_, v_argIdx_427_, v_callerIdx_428_, v_paramIdx_429_, v_a_430_, v_b_431_);
lean_dec(v_callerIdx_428_);
lean_dec(v_argIdx_427_);
lean_dec(v_calleeIdx_426_);
lean_dec(v_upperBound_425_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg___boxed(lean_object* v_upperBound_433_, lean_object* v_val_434_, lean_object* v_calleeIdx_435_, lean_object* v_argIdx_436_, lean_object* v_a_437_, lean_object* v_b_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(v_upperBound_433_, v_val_434_, v_calleeIdx_435_, v_argIdx_436_, v_a_437_, v_b_438_);
lean_dec(v_calleeIdx_435_);
lean_dec_ref(v_val_434_);
lean_dec(v_upperBound_433_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg___boxed(lean_object* v_upperBound_440_, lean_object* v_next_441_, lean_object* v_calleeIdx_442_, lean_object* v_argIdx_443_, lean_object* v_callerIdx_444_, lean_object* v_paramIdx_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(v_upperBound_440_, v_next_441_, v_calleeIdx_442_, v_argIdx_443_, v_callerIdx_444_, v_paramIdx_445_, v_a_446_, v_b_447_);
lean_dec(v_callerIdx_444_);
lean_dec(v_argIdx_443_);
lean_dec(v_calleeIdx_442_);
lean_dec(v_next_441_);
lean_dec(v_upperBound_440_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setCallerParam___boxed(lean_object* v_calleeIdx_449_, lean_object* v_argIdx_450_, lean_object* v_callerIdx_451_, lean_object* v_paramIdx_452_, lean_object* v_info_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_calleeIdx_449_, v_argIdx_450_, v_callerIdx_451_, v_paramIdx_452_, v_info_453_);
lean_dec(v_callerIdx_451_);
lean_dec(v_calleeIdx_449_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0(lean_object* v_upperBound_455_, lean_object* v_next_456_, lean_object* v_calleeIdx_457_, lean_object* v_argIdx_458_, lean_object* v_callerIdx_459_, lean_object* v_paramIdx_460_, lean_object* v_inst_461_, lean_object* v_R_462_, lean_object* v_a_463_, lean_object* v_b_464_, lean_object* v_c_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(v_upperBound_455_, v_next_456_, v_calleeIdx_457_, v_argIdx_458_, v_callerIdx_459_, v_paramIdx_460_, v_a_463_, v_b_464_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___boxed(lean_object* v_upperBound_467_, lean_object* v_next_468_, lean_object* v_calleeIdx_469_, lean_object* v_argIdx_470_, lean_object* v_callerIdx_471_, lean_object* v_paramIdx_472_, lean_object* v_inst_473_, lean_object* v_R_474_, lean_object* v_a_475_, lean_object* v_b_476_, lean_object* v_c_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0(v_upperBound_467_, v_next_468_, v_calleeIdx_469_, v_argIdx_470_, v_callerIdx_471_, v_paramIdx_472_, v_inst_473_, v_R_474_, v_a_475_, v_b_476_, v_c_477_);
lean_dec(v_callerIdx_471_);
lean_dec(v_argIdx_470_);
lean_dec(v_calleeIdx_469_);
lean_dec(v_next_468_);
lean_dec(v_upperBound_467_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1(lean_object* v_upperBound_479_, lean_object* v_calleeIdx_480_, lean_object* v_argIdx_481_, lean_object* v_callerIdx_482_, lean_object* v_paramIdx_483_, lean_object* v_inst_484_, lean_object* v_R_485_, lean_object* v_a_486_, lean_object* v_b_487_, lean_object* v_c_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(v_upperBound_479_, v_calleeIdx_480_, v_argIdx_481_, v_callerIdx_482_, v_paramIdx_483_, v_a_486_, v_b_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___boxed(lean_object* v_upperBound_490_, lean_object* v_calleeIdx_491_, lean_object* v_argIdx_492_, lean_object* v_callerIdx_493_, lean_object* v_paramIdx_494_, lean_object* v_inst_495_, lean_object* v_R_496_, lean_object* v_a_497_, lean_object* v_b_498_, lean_object* v_c_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1(v_upperBound_490_, v_calleeIdx_491_, v_argIdx_492_, v_callerIdx_493_, v_paramIdx_494_, v_inst_495_, v_R_496_, v_a_497_, v_b_498_, v_c_499_);
lean_dec(v_callerIdx_493_);
lean_dec(v_argIdx_492_);
lean_dec(v_calleeIdx_491_);
lean_dec(v_upperBound_490_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2(lean_object* v_upperBound_501_, lean_object* v_val_502_, lean_object* v_calleeIdx_503_, lean_object* v_argIdx_504_, lean_object* v_inst_505_, lean_object* v_R_506_, lean_object* v_a_507_, lean_object* v_b_508_, lean_object* v_c_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(v_upperBound_501_, v_val_502_, v_calleeIdx_503_, v_argIdx_504_, v_a_507_, v_b_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___boxed(lean_object* v_upperBound_511_, lean_object* v_val_512_, lean_object* v_calleeIdx_513_, lean_object* v_argIdx_514_, lean_object* v_inst_515_, lean_object* v_R_516_, lean_object* v_a_517_, lean_object* v_b_518_, lean_object* v_c_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2(v_upperBound_511_, v_val_512_, v_calleeIdx_513_, v_argIdx_514_, v_inst_515_, v_R_516_, v_a_517_, v_b_518_, v_c_519_);
lean_dec(v_calleeIdx_513_);
lean_dec_ref(v_val_512_);
lean_dec(v_upperBound_511_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_FixedParams_Info_format_spec__2(lean_object* v_a_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_nat_to_int(v_a_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1_spec__1(lean_object* v_x_523_, lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
if (lean_obj_tag(v_x_525_) == 0)
{
lean_dec(v_x_523_);
return v_x_524_;
}
else
{
lean_object* v_head_526_; lean_object* v_tail_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_536_; 
v_head_526_ = lean_ctor_get(v_x_525_, 0);
v_tail_527_ = lean_ctor_get(v_x_525_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v_x_525_);
if (v_isSharedCheck_536_ == 0)
{
v___x_529_ = v_x_525_;
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_tail_527_);
lean_inc(v_head_526_);
lean_dec(v_x_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
lean_inc(v_x_523_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 5);
lean_ctor_set(v___x_529_, 1, v_x_523_);
lean_ctor_set(v___x_529_, 0, v_x_524_);
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_x_524_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_x_523_);
v___x_532_ = v_reuseFailAlloc_535_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; 
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_head_526_);
v_x_524_ = v___x_533_;
v_x_525_ = v_tail_527_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
if (lean_obj_tag(v_x_537_) == 0)
{
lean_object* v___x_539_; 
lean_dec(v_x_538_);
v___x_539_ = lean_box(0);
return v___x_539_;
}
else
{
lean_object* v_tail_540_; 
v_tail_540_ = lean_ctor_get(v_x_537_, 1);
if (lean_obj_tag(v_tail_540_) == 0)
{
lean_object* v_head_541_; 
lean_dec(v_x_538_);
v_head_541_ = lean_ctor_get(v_x_537_, 0);
lean_inc(v_head_541_);
lean_dec_ref(v_x_537_);
return v_head_541_;
}
else
{
lean_object* v_head_542_; lean_object* v___x_543_; 
lean_inc(v_tail_540_);
v_head_542_ = lean_ctor_get(v_x_537_, 0);
lean_inc(v_head_542_);
lean_dec_ref(v_x_537_);
v___x_543_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1_spec__1(v_x_538_, v_head_542_, v_tail_540_);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0(lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
if (lean_obj_tag(v_a_550_) == 0)
{
lean_object* v___x_552_; 
v___x_552_ = l_List_reverse___redArg(v_a_551_);
return v___x_552_;
}
else
{
lean_object* v_head_553_; lean_object* v_tail_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_578_; 
v_head_553_ = lean_ctor_get(v_a_550_, 0);
v_tail_554_ = lean_ctor_get(v_a_550_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_a_550_);
if (v_isSharedCheck_578_ == 0)
{
v___x_556_ = v_a_550_;
v_isShared_557_ = v_isSharedCheck_578_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_tail_554_);
lean_inc(v_head_553_);
lean_dec(v_a_550_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_578_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___y_559_; 
if (lean_obj_tag(v_head_553_) == 0)
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__1));
v___y_559_ = v___x_564_;
goto v___jp_558_;
}
else
{
lean_object* v_val_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_577_; 
v_val_565_ = lean_ctor_get(v_head_553_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_head_553_);
if (v_isSharedCheck_577_ == 0)
{
v___x_567_ = v_head_553_;
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_val_565_);
lean_dec(v_head_553_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_569_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__3));
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_add(v_val_565_, v___x_570_);
lean_dec(v_val_565_);
v___x_572_ = l_Nat_reprFast(v___x_571_);
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 3);
lean_ctor_set(v___x_567_, 0, v___x_572_);
v___x_574_ = v___x_567_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_576_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; 
v___x_575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_569_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___y_559_ = v___x_575_;
goto v___jp_558_;
}
}
}
v___jp_558_:
{
lean_object* v___x_561_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v_a_551_);
lean_ctor_set(v___x_556_, 0, v___y_559_);
v___x_561_ = v___x_556_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___y_559_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_a_551_);
v___x_561_ = v_reuseFailAlloc_563_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
v_a_550_ = v_tail_554_;
v_a_551_ = v___x_561_;
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
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__4));
v___x_588_ = lean_string_length(v___x_587_);
return v___x_588_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__6, &l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__6_once, _init_l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__6);
v___x_590_ = lean_nat_to_int(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3(lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
if (lean_obj_tag(v_a_595_) == 0)
{
lean_object* v___x_597_; 
v___x_597_ = l_List_reverse___redArg(v_a_596_);
return v___x_597_;
}
else
{
lean_object* v_head_598_; lean_object* v_tail_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_624_; 
v_head_598_ = lean_ctor_get(v_a_595_, 0);
v_tail_599_ = lean_ctor_get(v_a_595_, 1);
v_isSharedCheck_624_ = !lean_is_exclusive(v_a_595_);
if (v_isSharedCheck_624_ == 0)
{
v___x_601_ = v_a_595_;
v_isShared_602_ = v_isSharedCheck_624_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_tail_599_);
lean_inc(v_head_598_);
lean_dec(v_a_595_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_624_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___y_604_; 
if (lean_obj_tag(v_head_598_) == 0)
{
lean_object* v___x_609_; 
v___x_609_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__1));
v___y_604_ = v___x_609_;
goto v___jp_603_;
}
else
{
lean_object* v_val_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; lean_object* v___x_623_; 
v_val_610_ = lean_ctor_get(v_head_598_, 0);
lean_inc(v_val_610_);
lean_dec_ref(v_head_598_);
v___x_611_ = lean_array_to_list(v_val_610_);
v___x_612_ = lean_box(0);
v___x_613_ = l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0(v___x_611_, v___x_612_);
v___x_614_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__3));
v___x_615_ = l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(v___x_613_, v___x_614_);
v___x_616_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7, &l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7_once, _init_l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7);
v___x_617_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__8));
v___x_618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_615_);
v___x_619_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_616_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = 0;
v___x_623_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*1, v___x_622_);
v___y_604_ = v___x_623_;
goto v___jp_603_;
}
v___jp_603_:
{
lean_object* v___x_606_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 1, v_a_596_);
lean_ctor_set(v___x_601_, 0, v___y_604_);
v___x_606_ = v___x_601_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___y_604_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_a_596_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
v_a_595_ = v_tail_599_;
v_a_596_ = v___x_606_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4(lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
if (lean_obj_tag(v_a_628_) == 0)
{
lean_object* v___x_630_; 
v___x_630_ = l_List_reverse___redArg(v_a_629_);
return v___x_630_;
}
else
{
lean_object* v_head_631_; lean_object* v_tail_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_647_; 
v_head_631_ = lean_ctor_get(v_a_628_, 0);
v_tail_632_ = lean_ctor_get(v_a_628_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_a_628_);
if (v_isSharedCheck_647_ == 0)
{
v___x_634_ = v_a_628_;
v_isShared_635_ = v_isSharedCheck_647_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_tail_632_);
lean_inc(v_head_631_);
lean_dec(v_a_628_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_647_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_636_ = lean_array_to_list(v_head_631_);
v___x_637_ = lean_box(0);
v___x_638_ = l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3(v___x_636_, v___x_637_);
v___x_639_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__3));
v___x_640_ = l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(v___x_638_, v___x_639_);
v___x_641_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4___closed__1));
v___x_642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v_a_629_);
lean_ctor_set(v___x_634_, 0, v___x_642_);
v___x_644_ = v___x_634_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_a_629_);
v___x_644_ = v_reuseFailAlloc_646_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
v_a_628_ = v_tail_632_;
v_a_629_ = v___x_644_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_format(lean_object* v_info_648_){
_start:
{
lean_object* v_graph_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_graph_649_ = lean_ctor_get(v_info_648_, 0);
lean_inc_ref(v_graph_649_);
lean_dec_ref(v_info_648_);
v___x_650_ = lean_array_to_list(v_graph_649_);
v___x_651_ = lean_box(0);
v___x_652_ = l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4(v___x_650_, v___x_651_);
v___x_653_ = lean_box(1);
v___x_654_ = l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(v___x_652_, v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0(lean_object* v_x_657_){
_start:
{
uint8_t v___x_658_; 
v___x_658_ = 0;
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0___boxed(lean_object* v_x_659_){
_start:
{
uint8_t v_res_660_; lean_object* v_r_661_; 
v_res_660_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0(v_x_659_);
lean_dec(v_x_659_);
v_r_661_ = lean_box(v_res_660_);
return v_r_661_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1(lean_object* v_fvarId_662_, lean_object* v_x_663_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = l_Lean_instBEqFVarId_beq(v_fvarId_662_, v_x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_665_, lean_object* v_x_666_){
_start:
{
uint8_t v_res_667_; lean_object* v_r_668_; 
v_res_667_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1(v_fvarId_665_, v_x_666_);
lean_dec(v_x_666_);
lean_dec(v_fvarId_665_);
v_r_668_ = lean_box(v_res_667_);
return v_r_668_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = lean_box(0);
v___x_671_ = lean_unsigned_to_nat(16u);
v___x_672_ = lean_mk_array(v___x_671_, v___x_670_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(lean_object* v_e_676_, lean_object* v_fvarId_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; uint8_t v_fst_682_; lean_object* v_mctx_683_; lean_object* v___y_701_; lean_object* v_mctx_706_; lean_object* v___f_707_; lean_object* v___f_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_680_ = lean_st_ref_get(v___y_678_);
v_mctx_706_ = lean_ctor_get(v___x_680_, 0);
lean_inc_ref_n(v_mctx_706_, 2);
lean_dec(v___x_680_);
v___f_707_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__0));
v___f_708_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_708_, 0, v_fvarId_677_);
v___x_709_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v_mctx_706_);
v___x_711_ = l_Lean_Expr_hasFVar(v_e_676_);
if (v___x_711_ == 0)
{
uint8_t v___x_712_; 
v___x_712_ = l_Lean_Expr_hasMVar(v_e_676_);
if (v___x_712_ == 0)
{
lean_dec_ref(v___x_710_);
lean_dec_ref(v___f_708_);
lean_dec_ref(v_e_676_);
v_fst_682_ = v___x_712_;
v_mctx_683_ = v_mctx_706_;
goto v___jp_681_;
}
else
{
lean_object* v___x_713_; 
lean_dec_ref(v_mctx_706_);
v___x_713_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_708_, v___f_707_, v_e_676_, v___x_710_);
v___y_701_ = v___x_713_;
goto v___jp_700_;
}
}
else
{
lean_object* v___x_714_; 
lean_dec_ref(v_mctx_706_);
v___x_714_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_708_, v___f_707_, v_e_676_, v___x_710_);
v___y_701_ = v___x_714_;
goto v___jp_700_;
}
v___jp_681_:
{
lean_object* v___x_684_; lean_object* v_cache_685_; lean_object* v_zetaDeltaFVarIds_686_; lean_object* v_postponed_687_; lean_object* v_diag_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_698_; 
v___x_684_ = lean_st_ref_take(v___y_678_);
v_cache_685_ = lean_ctor_get(v___x_684_, 1);
v_zetaDeltaFVarIds_686_ = lean_ctor_get(v___x_684_, 2);
v_postponed_687_ = lean_ctor_get(v___x_684_, 3);
v_diag_688_ = lean_ctor_get(v___x_684_, 4);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v___x_684_, 0);
lean_dec(v_unused_699_);
v___x_690_ = v___x_684_;
v_isShared_691_ = v_isSharedCheck_698_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_diag_688_);
lean_inc(v_postponed_687_);
lean_inc(v_zetaDeltaFVarIds_686_);
lean_inc(v_cache_685_);
lean_dec(v___x_684_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_698_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v_mctx_683_);
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_mctx_683_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_cache_685_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_zetaDeltaFVarIds_686_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v_postponed_687_);
lean_ctor_set(v_reuseFailAlloc_697_, 4, v_diag_688_);
v___x_693_ = v_reuseFailAlloc_697_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_st_ref_set(v___y_678_, v___x_693_);
v___x_695_ = lean_box(v_fst_682_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
}
}
v___jp_700_:
{
lean_object* v_snd_702_; lean_object* v_fst_703_; lean_object* v_mctx_704_; uint8_t v___x_705_; 
v_snd_702_ = lean_ctor_get(v___y_701_, 1);
lean_inc(v_snd_702_);
v_fst_703_ = lean_ctor_get(v___y_701_, 0);
lean_inc(v_fst_703_);
lean_dec_ref(v___y_701_);
v_mctx_704_ = lean_ctor_get(v_snd_702_, 1);
lean_inc_ref(v_mctx_704_);
lean_dec(v_snd_702_);
v___x_705_ = lean_unbox(v_fst_703_);
lean_dec(v_fst_703_);
v_fst_682_ = v___x_705_;
v_mctx_683_ = v_mctx_704_;
goto v___jp_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___boxed(lean_object* v_e_715_, lean_object* v_fvarId_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_e_715_, v_fvarId_716_, v___y_717_);
lean_dec(v___y_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0(lean_object* v_e_720_, lean_object* v_fvarId_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_e_720_, v_fvarId_721_, v___y_723_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___boxed(lean_object* v_e_728_, lean_object* v_fvarId_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0(v_e_728_, v_fvarId_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0(lean_object* v_k_736_, lean_object* v_b_737_, lean_object* v_c_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; 
lean_inc(v___y_742_);
lean_inc_ref(v___y_741_);
lean_inc(v___y_740_);
lean_inc_ref(v___y_739_);
v___x_744_ = lean_apply_7(v_k_736_, v_b_737_, v_c_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, lean_box(0));
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed(lean_object* v_k_745_, lean_object* v_b_746_, lean_object* v_c_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0(v_k_745_, v_b_746_, v_c_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(lean_object* v_e_754_, lean_object* v_k_755_, uint8_t v_cleanupAnnotations_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___f_762_; uint8_t v___x_763_; uint8_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___f_762_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_762_, 0, v_k_755_);
v___x_763_ = 1;
v___x_764_ = 0;
v___x_765_ = lean_box(0);
v___x_766_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_754_, v___x_763_, v___x_764_, v___x_763_, v___x_764_, v___x_765_, v___f_762_, v_cleanupAnnotations_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_a_775_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_766_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_766_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___boxed(lean_object* v_e_783_, lean_object* v_k_784_, lean_object* v_cleanupAnnotations_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_791_; lean_object* v_res_792_; 
v_cleanupAnnotations_boxed_791_ = lean_unbox(v_cleanupAnnotations_785_);
v_res_792_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_e_783_, v_k_784_, v_cleanupAnnotations_boxed_791_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3(lean_object* v_00_u03b1_793_, lean_object* v_e_794_, lean_object* v_k_795_, uint8_t v_cleanupAnnotations_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_e_794_, v_k_795_, v_cleanupAnnotations_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___boxed(lean_object* v_00_u03b1_803_, lean_object* v_e_804_, lean_object* v_k_805_, lean_object* v_cleanupAnnotations_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_812_; lean_object* v_res_813_; 
v_cleanupAnnotations_boxed_812_ = lean_unbox(v_cleanupAnnotations_806_);
v_res_813_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3(v_00_u03b1_803_, v_e_804_, v_k_805_, v_cleanupAnnotations_boxed_812_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(lean_object* v_upperBound_814_, lean_object* v_xs_815_, lean_object* v_next_816_, lean_object* v_a_817_, lean_object* v_b_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = lean_nat_dec_lt(v_a_817_, v_upperBound_814_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
lean_dec(v_a_817_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v_b_818_);
return v___x_825_;
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_array_fget_borrowed(v_xs_815_, v_a_817_);
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___x_826_);
v___x_827_ = lean_infer_type(v___x_826_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref(v___x_827_);
v___x_829_ = lean_array_fget_borrowed(v_xs_815_, v_next_816_);
v___x_830_ = l_Lean_Expr_fvarId_x21(v___x_829_);
v___x_831_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_a_828_, v___x_830_, v___y_820_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v_a_834_; uint8_t v___x_838_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref(v___x_831_);
v___x_838_ = lean_unbox(v_a_832_);
lean_dec(v_a_832_);
if (v___x_838_ == 0)
{
v_a_834_ = v_b_818_;
goto v___jp_833_;
}
else
{
lean_object* v___x_839_; 
lean_inc(v_a_817_);
v___x_839_ = lean_array_push(v_b_818_, v_a_817_);
v_a_834_ = v___x_839_;
goto v___jp_833_;
}
v___jp_833_:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(1u);
v___x_836_ = lean_nat_add(v_a_817_, v___x_835_);
lean_dec(v_a_817_);
v_a_817_ = v___x_836_;
v_b_818_ = v_a_834_;
goto _start;
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_b_818_);
lean_dec(v_a_817_);
v_a_840_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_831_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_831_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v_b_818_);
lean_dec(v_a_817_);
v_a_848_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_827_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_827_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg___boxed(lean_object* v_upperBound_856_, lean_object* v_xs_857_, lean_object* v_next_858_, lean_object* v_a_859_, lean_object* v_b_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v_upperBound_856_, v_xs_857_, v_next_858_, v_a_859_, v_b_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v_next_858_);
lean_dec_ref(v_xs_857_);
lean_dec(v_upperBound_856_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(lean_object* v_upperBound_869_, lean_object* v___x_870_, lean_object* v_xs_871_, lean_object* v_a_872_, lean_object* v_b_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = lean_nat_dec_lt(v_a_872_, v_upperBound_869_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
lean_dec(v_a_872_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v_b_873_);
return v___x_880_;
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_881_ = lean_unsigned_to_nat(1u);
v___x_882_ = lean_nat_add(v_a_872_, v___x_881_);
v___x_883_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg___closed__0));
lean_inc(v___x_882_);
v___x_884_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v___x_870_, v_xs_871_, v_a_872_, v___x_882_, v___x_883_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v_a_872_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref(v___x_884_);
v___x_886_ = lean_array_push(v_b_873_, v_a_885_);
v_a_872_ = v___x_882_;
v_b_873_ = v___x_886_;
goto _start;
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v___x_882_);
lean_dec_ref(v_b_873_);
v_a_888_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_884_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_884_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg___boxed(lean_object* v_upperBound_896_, lean_object* v___x_897_, lean_object* v_xs_898_, lean_object* v_a_899_, lean_object* v_b_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v_upperBound_896_, v___x_897_, v_xs_898_, v_a_899_, v_b_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec_ref(v_xs_898_);
lean_dec(v___x_897_);
lean_dec(v_upperBound_896_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___lam__0(lean_object* v_xs_909_, lean_object* v_x_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v_revDeps_918_; lean_object* v___x_919_; 
v___x_916_ = lean_array_get_size(v_xs_909_);
v___x_917_ = lean_unsigned_to_nat(0u);
v_revDeps_918_ = ((lean_object*)(l_Lean_Elab_getParamRevDeps___lam__0___closed__0));
v___x_919_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v___x_916_, v___x_916_, v_xs_909_, v___x_917_, v_revDeps_918_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___lam__0___boxed(lean_object* v_xs_920_, lean_object* v_x_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Elab_getParamRevDeps___lam__0(v_xs_920_, v_x_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec_ref(v_x_921_);
lean_dec_ref(v_xs_920_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps(lean_object* v_value_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___f_935_; uint8_t v___x_936_; lean_object* v___x_937_; 
v___f_935_ = ((lean_object*)(l_Lean_Elab_getParamRevDeps___closed__0));
v___x_936_ = 1;
v___x_937_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_929_, v___f_935_, v___x_936_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___boxed(lean_object* v_value_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Elab_getParamRevDeps(v_value_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1(lean_object* v_upperBound_945_, lean_object* v_xs_946_, lean_object* v_next_947_, lean_object* v_inst_948_, lean_object* v_R_949_, lean_object* v_a_950_, lean_object* v_b_951_, lean_object* v_c_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v_upperBound_945_, v_xs_946_, v_next_947_, v_a_950_, v_b_951_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___boxed(lean_object* v_upperBound_959_, lean_object* v_xs_960_, lean_object* v_next_961_, lean_object* v_inst_962_, lean_object* v_R_963_, lean_object* v_a_964_, lean_object* v_b_965_, lean_object* v_c_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1(v_upperBound_959_, v_xs_960_, v_next_961_, v_inst_962_, v_R_963_, v_a_964_, v_b_965_, v_c_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v_next_961_);
lean_dec_ref(v_xs_960_);
lean_dec(v_upperBound_959_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2(lean_object* v_upperBound_973_, lean_object* v___x_974_, lean_object* v_xs_975_, lean_object* v_inst_976_, lean_object* v_R_977_, lean_object* v_a_978_, lean_object* v_b_979_, lean_object* v_c_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v_upperBound_973_, v___x_974_, v_xs_975_, v_a_978_, v_b_979_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___boxed(lean_object* v_upperBound_987_, lean_object* v___x_988_, lean_object* v_xs_989_, lean_object* v_inst_990_, lean_object* v_R_991_, lean_object* v_a_992_, lean_object* v_b_993_, lean_object* v_c_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2(v_upperBound_987_, v___x_988_, v_xs_989_, v_inst_990_, v_R_991_, v_a_992_, v_b_993_, v_c_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec_ref(v_xs_989_);
lean_dec(v___x_988_);
lean_dec(v_upperBound_987_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_msg_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___f_1008_; lean_object* v___x_32777__overap_1009_; lean_object* v___x_1010_; 
v___f_1008_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_32777__overap_1009_ = lean_panic_fn_borrowed(v___f_1008_, v_msg_1002_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
v___x_1010_ = lean_apply_5(v___x_32777__overap_1009_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, lean_box(0));
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_msg_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_msg_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__0(lean_object* v_e_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_e_1018_);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__0___boxed(lean_object* v_e_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__0(v_e_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___lam__0(lean_object* v_00_u03b1_1033_, lean_object* v_x_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_apply_1(v_x_1034_, lean_box(0));
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___lam__0___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_x_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___lam__0(v_00_u03b1_1042_, v_x_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__0(lean_object* v_00_u03b1_1050_, lean_object* v_x_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_apply_1(v_x_1051_, lean_box(0));
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__0___boxed(lean_object* v_00_u03b1_1059_, lean_object* v_x_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__0(v_00_u03b1_1059_, v_x_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26_spec__27___redArg(lean_object* v_x_1067_, lean_object* v_x_1068_){
_start:
{
if (lean_obj_tag(v_x_1068_) == 0)
{
return v_x_1067_;
}
else
{
lean_object* v_key_1069_; lean_object* v_value_1070_; lean_object* v_tail_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1094_; 
v_key_1069_ = lean_ctor_get(v_x_1068_, 0);
v_value_1070_ = lean_ctor_get(v_x_1068_, 1);
v_tail_1071_ = lean_ctor_get(v_x_1068_, 2);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_x_1068_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1073_ = v_x_1068_;
v_isShared_1074_ = v_isSharedCheck_1094_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_tail_1071_);
lean_inc(v_value_1070_);
lean_inc(v_key_1069_);
lean_dec(v_x_1068_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1094_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; uint64_t v___x_1076_; uint64_t v___x_1077_; uint64_t v___x_1078_; uint64_t v_fold_1079_; uint64_t v___x_1080_; uint64_t v___x_1081_; uint64_t v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1075_ = lean_array_get_size(v_x_1067_);
v___x_1076_ = l_Lean_ExprStructEq_hash(v_key_1069_);
v___x_1077_ = 32ULL;
v___x_1078_ = lean_uint64_shift_right(v___x_1076_, v___x_1077_);
v_fold_1079_ = lean_uint64_xor(v___x_1076_, v___x_1078_);
v___x_1080_ = 16ULL;
v___x_1081_ = lean_uint64_shift_right(v_fold_1079_, v___x_1080_);
v___x_1082_ = lean_uint64_xor(v_fold_1079_, v___x_1081_);
v___x_1083_ = lean_uint64_to_usize(v___x_1082_);
v___x_1084_ = lean_usize_of_nat(v___x_1075_);
v___x_1085_ = ((size_t)1ULL);
v___x_1086_ = lean_usize_sub(v___x_1084_, v___x_1085_);
v___x_1087_ = lean_usize_land(v___x_1083_, v___x_1086_);
v___x_1088_ = lean_array_uget_borrowed(v_x_1067_, v___x_1087_);
lean_inc(v___x_1088_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 2, v___x_1088_);
v___x_1090_ = v___x_1073_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_key_1069_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_value_1070_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_array_uset(v_x_1067_, v___x_1087_, v___x_1090_);
v_x_1067_ = v___x_1091_;
v_x_1068_ = v_tail_1071_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26___redArg(lean_object* v_i_1095_, lean_object* v_source_1096_, lean_object* v_target_1097_){
_start:
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = lean_array_get_size(v_source_1096_);
v___x_1099_ = lean_nat_dec_lt(v_i_1095_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec_ref(v_source_1096_);
lean_dec(v_i_1095_);
return v_target_1097_;
}
else
{
lean_object* v_es_1100_; lean_object* v___x_1101_; lean_object* v_source_1102_; lean_object* v_target_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_es_1100_ = lean_array_fget(v_source_1096_, v_i_1095_);
v___x_1101_ = lean_box(0);
v_source_1102_ = lean_array_fset(v_source_1096_, v_i_1095_, v___x_1101_);
v_target_1103_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26_spec__27___redArg(v_target_1097_, v_es_1100_);
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_add(v_i_1095_, v___x_1104_);
lean_dec(v_i_1095_);
v_i_1095_ = v___x_1105_;
v_source_1096_ = v_source_1102_;
v_target_1097_ = v_target_1103_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25___redArg(lean_object* v_data_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v_nbuckets_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1108_ = lean_array_get_size(v_data_1107_);
v___x_1109_ = lean_unsigned_to_nat(2u);
v_nbuckets_1110_ = lean_nat_mul(v___x_1108_, v___x_1109_);
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = lean_box(0);
v___x_1113_ = lean_mk_array(v_nbuckets_1110_, v___x_1112_);
v___x_1114_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26___redArg(v___x_1111_, v_data_1107_, v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24___redArg(lean_object* v_a_1115_, lean_object* v_x_1116_){
_start:
{
if (lean_obj_tag(v_x_1116_) == 0)
{
uint8_t v___x_1117_; 
v___x_1117_ = 0;
return v___x_1117_;
}
else
{
lean_object* v_key_1118_; lean_object* v_tail_1119_; uint8_t v___x_1120_; 
v_key_1118_ = lean_ctor_get(v_x_1116_, 0);
v_tail_1119_ = lean_ctor_get(v_x_1116_, 2);
v___x_1120_ = l_Lean_ExprStructEq_beq(v_key_1118_, v_a_1115_);
if (v___x_1120_ == 0)
{
v_x_1116_ = v_tail_1119_;
goto _start;
}
else
{
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24___redArg___boxed(lean_object* v_a_1122_, lean_object* v_x_1123_){
_start:
{
uint8_t v_res_1124_; lean_object* v_r_1125_; 
v_res_1124_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24___redArg(v_a_1122_, v_x_1123_);
lean_dec(v_x_1123_);
lean_dec_ref(v_a_1122_);
v_r_1125_ = lean_box(v_res_1124_);
return v_r_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__26___redArg(lean_object* v_a_1126_, lean_object* v_b_1127_, lean_object* v_x_1128_){
_start:
{
if (lean_obj_tag(v_x_1128_) == 0)
{
lean_dec(v_b_1127_);
lean_dec_ref(v_a_1126_);
return v_x_1128_;
}
else
{
lean_object* v_key_1129_; lean_object* v_value_1130_; lean_object* v_tail_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1143_; 
v_key_1129_ = lean_ctor_get(v_x_1128_, 0);
v_value_1130_ = lean_ctor_get(v_x_1128_, 1);
v_tail_1131_ = lean_ctor_get(v_x_1128_, 2);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_x_1128_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1133_ = v_x_1128_;
v_isShared_1134_ = v_isSharedCheck_1143_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_tail_1131_);
lean_inc(v_value_1130_);
lean_inc(v_key_1129_);
lean_dec(v_x_1128_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1143_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
uint8_t v___x_1135_; 
v___x_1135_ = l_Lean_ExprStructEq_beq(v_key_1129_, v_a_1126_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1136_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__26___redArg(v_a_1126_, v_b_1127_, v_tail_1131_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 2, v___x_1136_);
v___x_1138_ = v___x_1133_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_key_1129_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_value_1130_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
else
{
lean_object* v___x_1141_; 
lean_dec(v_value_1130_);
lean_dec(v_key_1129_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 1, v_b_1127_);
lean_ctor_set(v___x_1133_, 0, v_a_1126_);
v___x_1141_ = v___x_1133_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1126_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_b_1127_);
lean_ctor_set(v_reuseFailAlloc_1142_, 2, v_tail_1131_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18___redArg(lean_object* v_m_1144_, lean_object* v_a_1145_, lean_object* v_b_1146_){
_start:
{
lean_object* v_size_1147_; lean_object* v_buckets_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1191_; 
v_size_1147_ = lean_ctor_get(v_m_1144_, 0);
v_buckets_1148_ = lean_ctor_get(v_m_1144_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_m_1144_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1150_ = v_m_1144_;
v_isShared_1151_ = v_isSharedCheck_1191_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_buckets_1148_);
lean_inc(v_size_1147_);
lean_dec(v_m_1144_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1191_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; uint64_t v___x_1153_; uint64_t v___x_1154_; uint64_t v___x_1155_; uint64_t v_fold_1156_; uint64_t v___x_1157_; uint64_t v___x_1158_; uint64_t v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; lean_object* v_bkt_1165_; uint8_t v___x_1166_; 
v___x_1152_ = lean_array_get_size(v_buckets_1148_);
v___x_1153_ = l_Lean_ExprStructEq_hash(v_a_1145_);
v___x_1154_ = 32ULL;
v___x_1155_ = lean_uint64_shift_right(v___x_1153_, v___x_1154_);
v_fold_1156_ = lean_uint64_xor(v___x_1153_, v___x_1155_);
v___x_1157_ = 16ULL;
v___x_1158_ = lean_uint64_shift_right(v_fold_1156_, v___x_1157_);
v___x_1159_ = lean_uint64_xor(v_fold_1156_, v___x_1158_);
v___x_1160_ = lean_uint64_to_usize(v___x_1159_);
v___x_1161_ = lean_usize_of_nat(v___x_1152_);
v___x_1162_ = ((size_t)1ULL);
v___x_1163_ = lean_usize_sub(v___x_1161_, v___x_1162_);
v___x_1164_ = lean_usize_land(v___x_1160_, v___x_1163_);
v_bkt_1165_ = lean_array_uget_borrowed(v_buckets_1148_, v___x_1164_);
v___x_1166_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24___redArg(v_a_1145_, v_bkt_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; lean_object* v_size_x27_1168_; lean_object* v___x_1169_; lean_object* v_buckets_x27_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1167_ = lean_unsigned_to_nat(1u);
v_size_x27_1168_ = lean_nat_add(v_size_1147_, v___x_1167_);
lean_dec(v_size_1147_);
lean_inc(v_bkt_1165_);
v___x_1169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1169_, 0, v_a_1145_);
lean_ctor_set(v___x_1169_, 1, v_b_1146_);
lean_ctor_set(v___x_1169_, 2, v_bkt_1165_);
v_buckets_x27_1170_ = lean_array_uset(v_buckets_1148_, v___x_1164_, v___x_1169_);
v___x_1171_ = lean_unsigned_to_nat(4u);
v___x_1172_ = lean_nat_mul(v_size_x27_1168_, v___x_1171_);
v___x_1173_ = lean_unsigned_to_nat(3u);
v___x_1174_ = lean_nat_div(v___x_1172_, v___x_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_array_get_size(v_buckets_x27_1170_);
v___x_1176_ = lean_nat_dec_le(v___x_1174_, v___x_1175_);
lean_dec(v___x_1174_);
if (v___x_1176_ == 0)
{
lean_object* v_val_1177_; lean_object* v___x_1179_; 
v_val_1177_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25___redArg(v_buckets_x27_1170_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 1, v_val_1177_);
lean_ctor_set(v___x_1150_, 0, v_size_x27_1168_);
v___x_1179_ = v___x_1150_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_size_x27_1168_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_val_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
else
{
lean_object* v___x_1182_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 1, v_buckets_x27_1170_);
lean_ctor_set(v___x_1150_, 0, v_size_x27_1168_);
v___x_1182_ = v___x_1150_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_size_x27_1168_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_buckets_x27_1170_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
else
{
lean_object* v___x_1184_; lean_object* v_buckets_x27_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
lean_inc(v_bkt_1165_);
v___x_1184_ = lean_box(0);
v_buckets_x27_1185_ = lean_array_uset(v_buckets_1148_, v___x_1164_, v___x_1184_);
v___x_1186_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__26___redArg(v_a_1145_, v_b_1146_, v_bkt_1165_);
v___x_1187_ = lean_array_uset(v_buckets_x27_1185_, v___x_1164_, v___x_1186_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 1, v___x_1187_);
v___x_1189_ = v___x_1150_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_size_1147_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__2(lean_object* v_a_1192_, lean_object* v_e_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1196_ = lean_st_ref_take(v_a_1192_);
v___x_1197_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18___redArg(v___x_1196_, v_e_1193_, v_a_1194_);
v___x_1198_ = lean_st_ref_set(v_a_1192_, v___x_1197_);
v___x_1199_ = lean_box(0);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__2___boxed(lean_object* v_a_1200_, lean_object* v_e_1201_, lean_object* v_a_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__2(v_a_1200_, v_e_1201_, v_a_1202_);
lean_dec(v_a_1200_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14___redArg(lean_object* v_a_1205_, lean_object* v_x_1206_){
_start:
{
if (lean_obj_tag(v_x_1206_) == 0)
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_box(0);
return v___x_1207_;
}
else
{
lean_object* v_key_1208_; lean_object* v_value_1209_; lean_object* v_tail_1210_; uint8_t v___x_1211_; 
v_key_1208_ = lean_ctor_get(v_x_1206_, 0);
v_value_1209_ = lean_ctor_get(v_x_1206_, 1);
v_tail_1210_ = lean_ctor_get(v_x_1206_, 2);
v___x_1211_ = l_Lean_ExprStructEq_beq(v_key_1208_, v_a_1205_);
if (v___x_1211_ == 0)
{
v_x_1206_ = v_tail_1210_;
goto _start;
}
else
{
lean_object* v___x_1213_; 
lean_inc(v_value_1209_);
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_value_1209_);
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14___redArg___boxed(lean_object* v_a_1214_, lean_object* v_x_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14___redArg(v_a_1214_, v_x_1215_);
lean_dec(v_x_1215_);
lean_dec_ref(v_a_1214_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12___redArg(lean_object* v_m_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_buckets_1219_; lean_object* v___x_1220_; uint64_t v___x_1221_; uint64_t v___x_1222_; uint64_t v___x_1223_; uint64_t v_fold_1224_; uint64_t v___x_1225_; uint64_t v___x_1226_; uint64_t v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_buckets_1219_ = lean_ctor_get(v_m_1217_, 1);
v___x_1220_ = lean_array_get_size(v_buckets_1219_);
v___x_1221_ = l_Lean_ExprStructEq_hash(v_a_1218_);
v___x_1222_ = 32ULL;
v___x_1223_ = lean_uint64_shift_right(v___x_1221_, v___x_1222_);
v_fold_1224_ = lean_uint64_xor(v___x_1221_, v___x_1223_);
v___x_1225_ = 16ULL;
v___x_1226_ = lean_uint64_shift_right(v_fold_1224_, v___x_1225_);
v___x_1227_ = lean_uint64_xor(v_fold_1224_, v___x_1226_);
v___x_1228_ = lean_uint64_to_usize(v___x_1227_);
v___x_1229_ = lean_usize_of_nat(v___x_1220_);
v___x_1230_ = ((size_t)1ULL);
v___x_1231_ = lean_usize_sub(v___x_1229_, v___x_1230_);
v___x_1232_ = lean_usize_land(v___x_1228_, v___x_1231_);
v___x_1233_ = lean_array_uget_borrowed(v_buckets_1219_, v___x_1232_);
v___x_1234_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14___redArg(v_a_1218_, v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12___redArg___boxed(lean_object* v_m_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12___redArg(v_m_1235_, v_a_1236_);
lean_dec_ref(v_a_1236_);
lean_dec_ref(v_m_1235_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg___lam__0(lean_object* v_k_1238_, lean_object* v___y_1239_, lean_object* v_b_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1239_);
v___x_1246_ = lean_apply_7(v_k_1238_, v_b_1240_, v___y_1239_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, lean_box(0));
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg___lam__0___boxed(lean_object* v_k_1247_, lean_object* v___y_1248_, lean_object* v_b_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg___lam__0(v_k_1247_, v___y_1248_, v_b_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1248_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg(lean_object* v_name_1256_, uint8_t v_bi_1257_, lean_object* v_type_1258_, lean_object* v_k_1259_, uint8_t v_kind_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___f_1267_; lean_object* v___x_1268_; 
lean_inc(v___y_1261_);
v___f_1267_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1267_, 0, v_k_1259_);
lean_closure_set(v___f_1267_, 1, v___y_1261_);
v___x_1268_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1256_, v_bi_1257_, v_type_1258_, v___f_1267_, v_kind_1260_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1268_) == 0)
{
return v___x_1268_;
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg___boxed(lean_object* v_name_1277_, lean_object* v_bi_1278_, lean_object* v_type_1279_, lean_object* v_k_1280_, lean_object* v_kind_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
uint8_t v_bi_boxed_1288_; uint8_t v_kind_boxed_1289_; lean_object* v_res_1290_; 
v_bi_boxed_1288_ = lean_unbox(v_bi_1278_);
v_kind_boxed_1289_ = lean_unbox(v_kind_1281_);
v_res_1290_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg(v_name_1277_, v_bi_boxed_1288_, v_type_1279_, v_k_1280_, v_kind_boxed_1289_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__2(lean_object* v___x_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1291_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__2___boxed(lean_object* v___x_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__2(v___x_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19___redArg(lean_object* v_name_1305_, lean_object* v_type_1306_, lean_object* v_val_1307_, lean_object* v_k_1308_, uint8_t v_nondep_1309_, uint8_t v_kind_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___f_1317_; lean_object* v___x_1318_; 
lean_inc(v___y_1311_);
v___f_1317_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1317_, 0, v_k_1308_);
lean_closure_set(v___f_1317_, 1, v___y_1311_);
v___x_1318_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1305_, v_type_1306_, v_val_1307_, v___f_1317_, v_nondep_1309_, v_kind_1310_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1318_) == 0)
{
return v___x_1318_;
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19___redArg___boxed(lean_object* v_name_1327_, lean_object* v_type_1328_, lean_object* v_val_1329_, lean_object* v_k_1330_, lean_object* v_nondep_1331_, lean_object* v_kind_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v_nondep_boxed_1339_; uint8_t v_kind_boxed_1340_; lean_object* v_res_1341_; 
v_nondep_boxed_1339_ = lean_unbox(v_nondep_1331_);
v_kind_boxed_1340_ = lean_unbox(v_kind_1332_);
v_res_1341_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19___redArg(v_name_1327_, v_type_1328_, v_val_1329_, v_k_1330_, v_nondep_boxed_1339_, v_kind_boxed_1340_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
return v_res_1341_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = l_Lean_maxRecDepthErrorMessage;
v___x_1348_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__4(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__3);
v___x_1350_ = l_Lean_MessageData_ofFormat(v___x_1349_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__4);
v___x_1352_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__2));
v___x_1353_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v___x_1351_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg(lean_object* v_ref_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___closed__5);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v_ref_1354_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg___boxed(lean_object* v_ref_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg(v_ref_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___redArg(lean_object* v_x_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___y_1370_; lean_object* v_fileName_1379_; lean_object* v_fileMap_1380_; lean_object* v_options_1381_; lean_object* v_currRecDepth_1382_; lean_object* v_maxRecDepth_1383_; lean_object* v_ref_1384_; lean_object* v_currNamespace_1385_; lean_object* v_openDecls_1386_; lean_object* v_initHeartbeats_1387_; lean_object* v_maxHeartbeats_1388_; lean_object* v_quotContext_1389_; lean_object* v_currMacroScope_1390_; uint8_t v_diag_1391_; lean_object* v_cancelTk_x3f_1392_; uint8_t v_suppressElabErrors_1393_; lean_object* v_inheritedTraceOptions_1394_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v_fileName_1379_ = lean_ctor_get(v___y_1366_, 0);
v_fileMap_1380_ = lean_ctor_get(v___y_1366_, 1);
v_options_1381_ = lean_ctor_get(v___y_1366_, 2);
v_currRecDepth_1382_ = lean_ctor_get(v___y_1366_, 3);
v_maxRecDepth_1383_ = lean_ctor_get(v___y_1366_, 4);
v_ref_1384_ = lean_ctor_get(v___y_1366_, 5);
v_currNamespace_1385_ = lean_ctor_get(v___y_1366_, 6);
v_openDecls_1386_ = lean_ctor_get(v___y_1366_, 7);
v_initHeartbeats_1387_ = lean_ctor_get(v___y_1366_, 8);
v_maxHeartbeats_1388_ = lean_ctor_get(v___y_1366_, 9);
v_quotContext_1389_ = lean_ctor_get(v___y_1366_, 10);
v_currMacroScope_1390_ = lean_ctor_get(v___y_1366_, 11);
v_diag_1391_ = lean_ctor_get_uint8(v___y_1366_, sizeof(void*)*14);
v_cancelTk_x3f_1392_ = lean_ctor_get(v___y_1366_, 12);
v_suppressElabErrors_1393_ = lean_ctor_get_uint8(v___y_1366_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1394_ = lean_ctor_get(v___y_1366_, 13);
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = lean_nat_dec_eq(v_maxRecDepth_1383_, v___x_1400_);
if (v___x_1401_ == 0)
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_nat_dec_eq(v_currRecDepth_1382_, v_maxRecDepth_1383_);
if (v___x_1402_ == 0)
{
goto v___jp_1395_;
}
else
{
lean_object* v___x_1403_; 
lean_dec_ref(v_x_1362_);
lean_inc(v_ref_1384_);
v___x_1403_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg(v_ref_1384_);
v___y_1370_ = v___x_1403_;
goto v___jp_1369_;
}
}
else
{
goto v___jp_1395_;
}
v___jp_1369_:
{
if (lean_obj_tag(v___y_1370_) == 0)
{
return v___y_1370_;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_a_1371_ = lean_ctor_get(v___y_1370_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___y_1370_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___y_1370_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___y_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
v___jp_1395_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_unsigned_to_nat(1u);
v___x_1397_ = lean_nat_add(v_currRecDepth_1382_, v___x_1396_);
lean_inc_ref(v_inheritedTraceOptions_1394_);
lean_inc(v_cancelTk_x3f_1392_);
lean_inc(v_currMacroScope_1390_);
lean_inc(v_quotContext_1389_);
lean_inc(v_maxHeartbeats_1388_);
lean_inc(v_initHeartbeats_1387_);
lean_inc(v_openDecls_1386_);
lean_inc(v_currNamespace_1385_);
lean_inc(v_ref_1384_);
lean_inc(v_maxRecDepth_1383_);
lean_inc_ref(v_options_1381_);
lean_inc_ref(v_fileMap_1380_);
lean_inc_ref(v_fileName_1379_);
v___x_1398_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1398_, 0, v_fileName_1379_);
lean_ctor_set(v___x_1398_, 1, v_fileMap_1380_);
lean_ctor_set(v___x_1398_, 2, v_options_1381_);
lean_ctor_set(v___x_1398_, 3, v___x_1397_);
lean_ctor_set(v___x_1398_, 4, v_maxRecDepth_1383_);
lean_ctor_set(v___x_1398_, 5, v_ref_1384_);
lean_ctor_set(v___x_1398_, 6, v_currNamespace_1385_);
lean_ctor_set(v___x_1398_, 7, v_openDecls_1386_);
lean_ctor_set(v___x_1398_, 8, v_initHeartbeats_1387_);
lean_ctor_set(v___x_1398_, 9, v_maxHeartbeats_1388_);
lean_ctor_set(v___x_1398_, 10, v_quotContext_1389_);
lean_ctor_set(v___x_1398_, 11, v_currMacroScope_1390_);
lean_ctor_set(v___x_1398_, 12, v_cancelTk_x3f_1392_);
lean_ctor_set(v___x_1398_, 13, v_inheritedTraceOptions_1394_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*14, v_diag_1391_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*14 + 1, v_suppressElabErrors_1393_);
lean_inc(v___y_1367_);
lean_inc(v___y_1365_);
lean_inc_ref(v___y_1364_);
lean_inc(v___y_1363_);
v___x_1399_ = lean_apply_6(v_x_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___x_1398_, v___y_1367_, lean_box(0));
v___y_1370_ = v___x_1399_;
goto v___jp_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___redArg___boxed(lean_object* v_x_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___redArg(v_x_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___lam__0(lean_object* v_fvars_1415_, lean_object* v_pre_1416_, lean_object* v_post_1417_, uint8_t v_usedLetOnly_1418_, uint8_t v_skipConstInApp_1419_, uint8_t v_skipInstances_1420_, lean_object* v_body_1421_, lean_object* v_x_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_array_push(v_fvars_1415_, v_x_1422_);
v___x_1430_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14(v_pre_1416_, v_post_1417_, v_usedLetOnly_1418_, v_skipConstInApp_1419_, v_skipInstances_1420_, v___x_1429_, v_body_1421_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___lam__0___boxed(lean_object* v_fvars_1431_, lean_object* v_pre_1432_, lean_object* v_post_1433_, lean_object* v_usedLetOnly_1434_, lean_object* v_skipConstInApp_1435_, lean_object* v_skipInstances_1436_, lean_object* v_body_1437_, lean_object* v_x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v_usedLetOnly_boxed_1445_; uint8_t v_skipConstInApp_boxed_1446_; uint8_t v_skipInstances_boxed_1447_; lean_object* v_res_1448_; 
v_usedLetOnly_boxed_1445_ = lean_unbox(v_usedLetOnly_1434_);
v_skipConstInApp_boxed_1446_ = lean_unbox(v_skipConstInApp_1435_);
v_skipInstances_boxed_1447_ = lean_unbox(v_skipInstances_1436_);
v_res_1448_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___lam__0(v_fvars_1431_, v_pre_1432_, v_post_1433_, v_usedLetOnly_boxed_1445_, v_skipConstInApp_boxed_1446_, v_skipInstances_boxed_1447_, v_body_1437_, v_x_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(lean_object* v_pre_1449_, lean_object* v_post_1450_, uint8_t v_usedLetOnly_1451_, uint8_t v_skipConstInApp_1452_, uint8_t v_skipInstances_1453_, lean_object* v_e_1454_, lean_object* v_a_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___x_1461_; 
lean_inc_ref(v_post_1450_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
lean_inc_ref(v_e_1454_);
v___x_1461_ = lean_apply_6(v_post_1450_, v_e_1454_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, lean_box(0));
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1480_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1480_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1480_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
switch(lean_obj_tag(v_a_1462_))
{
case 0:
{
lean_object* v_e_1466_; lean_object* v___x_1468_; 
lean_dec_ref(v_e_1454_);
lean_dec_ref(v_post_1450_);
lean_dec_ref(v_pre_1449_);
v_e_1466_ = lean_ctor_get(v_a_1462_, 0);
lean_inc_ref(v_e_1466_);
lean_dec_ref(v_a_1462_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v_e_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_e_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
case 1:
{
lean_object* v_e_1470_; lean_object* v___x_1471_; 
lean_del_object(v___x_1464_);
lean_dec_ref(v_e_1454_);
v_e_1470_ = lean_ctor_get(v_a_1462_, 0);
lean_inc_ref(v_e_1470_);
lean_dec_ref(v_a_1462_);
v___x_1471_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1449_, v_post_1450_, v_usedLetOnly_1451_, v_skipConstInApp_1452_, v_skipInstances_1453_, v_e_1470_, v_a_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1471_;
}
default: 
{
lean_object* v_e_x3f_1472_; 
lean_dec_ref(v_post_1450_);
lean_dec_ref(v_pre_1449_);
v_e_x3f_1472_ = lean_ctor_get(v_a_1462_, 0);
lean_inc(v_e_x3f_1472_);
lean_dec_ref(v_a_1462_);
if (lean_obj_tag(v_e_x3f_1472_) == 0)
{
lean_object* v___x_1474_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v_e_1454_);
v___x_1474_ = v___x_1464_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_e_1454_);
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
lean_object* v_val_1476_; lean_object* v___x_1478_; 
lean_dec_ref(v_e_1454_);
v_val_1476_ = lean_ctor_get(v_e_x3f_1472_, 0);
lean_inc(v_val_1476_);
lean_dec_ref(v_e_x3f_1472_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v_val_1476_);
v___x_1478_ = v___x_1464_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_val_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v_e_1454_);
lean_dec_ref(v_post_1450_);
lean_dec_ref(v_pre_1449_);
v_a_1481_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1461_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1461_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14(lean_object* v_pre_1489_, lean_object* v_post_1490_, uint8_t v_usedLetOnly_1491_, uint8_t v_skipConstInApp_1492_, uint8_t v_skipInstances_1493_, lean_object* v_fvars_1494_, lean_object* v_e_1495_, lean_object* v_a_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
if (lean_obj_tag(v_e_1495_) == 6)
{
lean_object* v_binderName_1502_; lean_object* v_binderType_1503_; lean_object* v_body_1504_; uint8_t v_binderInfo_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_binderName_1502_ = lean_ctor_get(v_e_1495_, 0);
lean_inc(v_binderName_1502_);
v_binderType_1503_ = lean_ctor_get(v_e_1495_, 1);
lean_inc_ref(v_binderType_1503_);
v_body_1504_ = lean_ctor_get(v_e_1495_, 2);
lean_inc_ref(v_body_1504_);
v_binderInfo_1505_ = lean_ctor_get_uint8(v_e_1495_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1495_);
v___x_1506_ = lean_expr_instantiate_rev(v_binderType_1503_, v_fvars_1494_);
lean_dec_ref(v_binderType_1503_);
lean_inc_ref(v_post_1490_);
lean_inc_ref(v_pre_1489_);
v___x_1507_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1489_, v_post_1490_, v_usedLetOnly_1491_, v_skipConstInApp_1492_, v_skipInstances_1493_, v___x_1506_, v_a_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___f_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref(v___x_1507_);
v___x_1509_ = lean_box(v_usedLetOnly_1491_);
v___x_1510_ = lean_box(v_skipConstInApp_1492_);
v___x_1511_ = lean_box(v_skipInstances_1493_);
v___f_1512_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1512_, 0, v_fvars_1494_);
lean_closure_set(v___f_1512_, 1, v_pre_1489_);
lean_closure_set(v___f_1512_, 2, v_post_1490_);
lean_closure_set(v___f_1512_, 3, v___x_1509_);
lean_closure_set(v___f_1512_, 4, v___x_1510_);
lean_closure_set(v___f_1512_, 5, v___x_1511_);
lean_closure_set(v___f_1512_, 6, v_body_1504_);
v___x_1513_ = 0;
v___x_1514_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg(v_binderName_1502_, v_binderInfo_1505_, v_a_1508_, v___f_1512_, v___x_1513_, v_a_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
return v___x_1514_;
}
else
{
lean_dec_ref(v_body_1504_);
lean_dec(v_binderName_1502_);
lean_dec_ref(v_fvars_1494_);
lean_dec_ref(v_post_1490_);
lean_dec_ref(v_pre_1489_);
return v___x_1507_;
}
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_expr_instantiate_rev(v_e_1495_, v_fvars_1494_);
lean_dec_ref(v_e_1495_);
lean_inc_ref(v_post_1490_);
lean_inc_ref(v_pre_1489_);
v___x_1516_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1489_, v_post_1490_, v_usedLetOnly_1491_, v_skipConstInApp_1492_, v_skipInstances_1493_, v___x_1515_, v_a_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; uint8_t v___x_1518_; uint8_t v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v___x_1516_);
v___x_1518_ = 0;
v___x_1519_ = 1;
v___x_1520_ = 1;
v___x_1521_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1494_, v_a_1517_, v___x_1518_, v_usedLetOnly_1491_, v___x_1518_, v___x_1519_, v___x_1520_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec_ref(v_fvars_1494_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1489_, v_post_1490_, v_usedLetOnly_1491_, v_skipConstInApp_1492_, v_skipInstances_1493_, v_a_1522_, v_a_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
return v___x_1523_;
}
else
{
lean_dec_ref(v_post_1490_);
lean_dec_ref(v_pre_1489_);
return v___x_1521_;
}
}
else
{
lean_dec_ref(v_fvars_1494_);
lean_dec_ref(v_post_1490_);
lean_dec_ref(v_pre_1489_);
return v___x_1516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___lam__0(lean_object* v_fvars_1524_, lean_object* v_pre_1525_, lean_object* v_post_1526_, uint8_t v_usedLetOnly_1527_, uint8_t v_skipConstInApp_1528_, uint8_t v_skipInstances_1529_, lean_object* v_body_1530_, lean_object* v_x_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_array_push(v_fvars_1524_, v_x_1531_);
v___x_1539_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15(v_pre_1525_, v_post_1526_, v_usedLetOnly_1527_, v_skipConstInApp_1528_, v_skipInstances_1529_, v___x_1538_, v_body_1530_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___lam__0___boxed(lean_object* v_fvars_1540_, lean_object* v_pre_1541_, lean_object* v_post_1542_, lean_object* v_usedLetOnly_1543_, lean_object* v_skipConstInApp_1544_, lean_object* v_skipInstances_1545_, lean_object* v_body_1546_, lean_object* v_x_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
uint8_t v_usedLetOnly_boxed_1554_; uint8_t v_skipConstInApp_boxed_1555_; uint8_t v_skipInstances_boxed_1556_; lean_object* v_res_1557_; 
v_usedLetOnly_boxed_1554_ = lean_unbox(v_usedLetOnly_1543_);
v_skipConstInApp_boxed_1555_ = lean_unbox(v_skipConstInApp_1544_);
v_skipInstances_boxed_1556_ = lean_unbox(v_skipInstances_1545_);
v_res_1557_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___lam__0(v_fvars_1540_, v_pre_1541_, v_post_1542_, v_usedLetOnly_boxed_1554_, v_skipConstInApp_boxed_1555_, v_skipInstances_boxed_1556_, v_body_1546_, v_x_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15(lean_object* v_pre_1558_, lean_object* v_post_1559_, uint8_t v_usedLetOnly_1560_, uint8_t v_skipConstInApp_1561_, uint8_t v_skipInstances_1562_, lean_object* v_fvars_1563_, lean_object* v_e_1564_, lean_object* v_a_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
if (lean_obj_tag(v_e_1564_) == 8)
{
lean_object* v_declName_1571_; lean_object* v_type_1572_; lean_object* v_value_1573_; lean_object* v_body_1574_; uint8_t v_nondep_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_declName_1571_ = lean_ctor_get(v_e_1564_, 0);
lean_inc(v_declName_1571_);
v_type_1572_ = lean_ctor_get(v_e_1564_, 1);
lean_inc_ref(v_type_1572_);
v_value_1573_ = lean_ctor_get(v_e_1564_, 2);
lean_inc_ref(v_value_1573_);
v_body_1574_ = lean_ctor_get(v_e_1564_, 3);
lean_inc_ref(v_body_1574_);
v_nondep_1575_ = lean_ctor_get_uint8(v_e_1564_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1564_);
v___x_1576_ = lean_expr_instantiate_rev(v_type_1572_, v_fvars_1563_);
lean_dec_ref(v_type_1572_);
lean_inc_ref(v_post_1559_);
lean_inc_ref(v_pre_1558_);
v___x_1577_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1558_, v_post_1559_, v_usedLetOnly_1560_, v_skipConstInApp_1561_, v_skipInstances_1562_, v___x_1576_, v_a_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = lean_expr_instantiate_rev(v_value_1573_, v_fvars_1563_);
lean_dec_ref(v_value_1573_);
lean_inc_ref(v_post_1559_);
lean_inc_ref(v_pre_1558_);
v___x_1580_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1558_, v_post_1559_, v_usedLetOnly_1560_, v_skipConstInApp_1561_, v_skipInstances_1562_, v___x_1579_, v_a_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___f_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref(v___x_1580_);
v___x_1582_ = lean_box(v_usedLetOnly_1560_);
v___x_1583_ = lean_box(v_skipConstInApp_1561_);
v___x_1584_ = lean_box(v_skipInstances_1562_);
v___f_1585_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1585_, 0, v_fvars_1563_);
lean_closure_set(v___f_1585_, 1, v_pre_1558_);
lean_closure_set(v___f_1585_, 2, v_post_1559_);
lean_closure_set(v___f_1585_, 3, v___x_1582_);
lean_closure_set(v___f_1585_, 4, v___x_1583_);
lean_closure_set(v___f_1585_, 5, v___x_1584_);
lean_closure_set(v___f_1585_, 6, v_body_1574_);
v___x_1586_ = 0;
v___x_1587_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19___redArg(v_declName_1571_, v_a_1578_, v_a_1581_, v___f_1585_, v_nondep_1575_, v___x_1586_, v_a_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
return v___x_1587_;
}
else
{
lean_dec(v_a_1578_);
lean_dec_ref(v_body_1574_);
lean_dec(v_declName_1571_);
lean_dec_ref(v_fvars_1563_);
lean_dec_ref(v_post_1559_);
lean_dec_ref(v_pre_1558_);
return v___x_1580_;
}
}
else
{
lean_dec_ref(v_body_1574_);
lean_dec_ref(v_value_1573_);
lean_dec(v_declName_1571_);
lean_dec_ref(v_fvars_1563_);
lean_dec_ref(v_post_1559_);
lean_dec_ref(v_pre_1558_);
return v___x_1577_;
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_expr_instantiate_rev(v_e_1564_, v_fvars_1563_);
lean_dec_ref(v_e_1564_);
lean_inc_ref(v_post_1559_);
lean_inc_ref(v_pre_1558_);
v___x_1589_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1558_, v_post_1559_, v_usedLetOnly_1560_, v_skipConstInApp_1561_, v_skipInstances_1562_, v___x_1588_, v_a_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; uint8_t v___x_1591_; uint8_t v___x_1592_; lean_object* v___x_1593_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = 0;
v___x_1592_ = 1;
v___x_1593_ = l_Lean_Meta_mkLetFVars(v_fvars_1563_, v_a_1590_, v_usedLetOnly_1560_, v___x_1591_, v___x_1592_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec_ref(v_fvars_1563_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1595_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref(v___x_1593_);
v___x_1595_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1558_, v_post_1559_, v_usedLetOnly_1560_, v_skipConstInApp_1561_, v_skipInstances_1562_, v_a_1594_, v_a_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
return v___x_1595_;
}
else
{
lean_dec_ref(v_post_1559_);
lean_dec_ref(v_pre_1558_);
return v___x_1593_;
}
}
else
{
lean_dec_ref(v_fvars_1563_);
lean_dec_ref(v_post_1559_);
lean_dec_ref(v_pre_1558_);
return v___x_1589_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1596_; lean_object* v_dummy_1597_; 
v___x_1596_ = lean_box(0);
v_dummy_1597_ = l_Lean_Expr_sort___override(v___x_1596_);
return v_dummy_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__9(lean_object* v_pre_1598_, lean_object* v_post_1599_, uint8_t v_usedLetOnly_1600_, uint8_t v_skipConstInApp_1601_, uint8_t v_skipInstances_1602_, size_t v_sz_1603_, size_t v_i_1604_, lean_object* v_bs_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
uint8_t v___x_1612_; 
v___x_1612_ = lean_usize_dec_lt(v_i_1604_, v_sz_1603_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
lean_dec_ref(v_post_1599_);
lean_dec_ref(v_pre_1598_);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v_bs_1605_);
return v___x_1613_;
}
else
{
lean_object* v_v_1614_; lean_object* v___x_1615_; 
v_v_1614_ = lean_array_uget_borrowed(v_bs_1605_, v_i_1604_);
lean_inc(v_v_1614_);
lean_inc_ref(v_post_1599_);
lean_inc_ref(v_pre_1598_);
v___x_1615_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1598_, v_post_1599_, v_usedLetOnly_1600_, v_skipConstInApp_1601_, v_skipInstances_1602_, v_v_1614_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; lean_object* v_bs_x27_1618_; size_t v___x_1619_; size_t v___x_1620_; lean_object* v___x_1621_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref(v___x_1615_);
v___x_1617_ = lean_unsigned_to_nat(0u);
v_bs_x27_1618_ = lean_array_uset(v_bs_1605_, v_i_1604_, v___x_1617_);
v___x_1619_ = ((size_t)1ULL);
v___x_1620_ = lean_usize_add(v_i_1604_, v___x_1619_);
v___x_1621_ = lean_array_uset(v_bs_x27_1618_, v_i_1604_, v_a_1616_);
v_i_1604_ = v___x_1620_;
v_bs_1605_ = v___x_1621_;
goto _start;
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref(v_bs_1605_);
lean_dec_ref(v_post_1599_);
lean_dec_ref(v_pre_1598_);
v_a_1623_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1615_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1615_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__0(lean_object* v_pre_1631_, lean_object* v_post_1632_, uint8_t v_usedLetOnly_1633_, uint8_t v_skipConstInApp_1634_, uint8_t v_skipInstances_1635_, lean_object* v___x_1636_, lean_object* v___y_1637_, lean_object* v_b_1638_, lean_object* v_a_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1631_, v_post_1632_, v_usedLetOnly_1633_, v_skipConstInApp_1634_, v_skipInstances_1635_, v___x_1636_, v___y_1637_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1655_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1655_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1655_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1650_ = lean_array_fset(v_b_1638_, v_a_1639_, v_a_1646_);
v___x_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1651_);
v___x_1653_ = v___x_1648_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v_b_1638_);
v_a_1656_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1645_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1645_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__0___boxed(lean_object* v_pre_1664_, lean_object* v_post_1665_, lean_object* v_usedLetOnly_1666_, lean_object* v_skipConstInApp_1667_, lean_object* v_skipInstances_1668_, lean_object* v___x_1669_, lean_object* v___y_1670_, lean_object* v_b_1671_, lean_object* v_a_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
uint8_t v_usedLetOnly_boxed_1678_; uint8_t v_skipConstInApp_boxed_1679_; uint8_t v_skipInstances_boxed_1680_; lean_object* v_res_1681_; 
v_usedLetOnly_boxed_1678_ = lean_unbox(v_usedLetOnly_1666_);
v_skipConstInApp_boxed_1679_ = lean_unbox(v_skipConstInApp_1667_);
v_skipInstances_boxed_1680_ = lean_unbox(v_skipInstances_1668_);
v_res_1681_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__0(v_pre_1664_, v_post_1665_, v_usedLetOnly_boxed_1678_, v_skipConstInApp_boxed_1679_, v_skipInstances_boxed_1680_, v___x_1669_, v___y_1670_, v_b_1671_, v_a_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v_a_1672_);
lean_dec(v___y_1670_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg(lean_object* v_upperBound_1682_, lean_object* v___x_1683_, lean_object* v_pre_1684_, lean_object* v_post_1685_, uint8_t v_usedLetOnly_1686_, uint8_t v_skipConstInApp_1687_, uint8_t v_skipInstances_1688_, lean_object* v_a_1689_, lean_object* v_b_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___y_1698_; uint8_t v___x_1721_; 
v___x_1721_ = lean_nat_dec_lt(v_a_1689_, v_upperBound_1682_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_dec(v_a_1689_);
lean_dec_ref(v_post_1685_);
lean_dec_ref(v_pre_1684_);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_b_1690_);
return v___x_1722_;
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1723_ = lean_array_fget_borrowed(v_b_1690_, v_a_1689_);
v___x_1724_ = lean_array_get_size(v___x_1683_);
v___x_1725_ = lean_nat_dec_lt(v_a_1689_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___f_1729_; 
lean_inc(v___x_1723_);
v___x_1726_ = lean_box(v_usedLetOnly_1686_);
v___x_1727_ = lean_box(v_skipConstInApp_1687_);
v___x_1728_ = lean_box(v_skipInstances_1688_);
lean_inc(v_a_1689_);
lean_inc(v___y_1691_);
lean_inc_ref(v_post_1685_);
lean_inc_ref(v_pre_1684_);
v___f_1729_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1729_, 0, v_pre_1684_);
lean_closure_set(v___f_1729_, 1, v_post_1685_);
lean_closure_set(v___f_1729_, 2, v___x_1726_);
lean_closure_set(v___f_1729_, 3, v___x_1727_);
lean_closure_set(v___f_1729_, 4, v___x_1728_);
lean_closure_set(v___f_1729_, 5, v___x_1723_);
lean_closure_set(v___f_1729_, 6, v___y_1691_);
lean_closure_set(v___f_1729_, 7, v_b_1690_);
lean_closure_set(v___f_1729_, 8, v_a_1689_);
v___y_1698_ = v___f_1729_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1730_; uint8_t v_isInstance_1731_; 
v___x_1730_ = lean_array_fget_borrowed(v___x_1683_, v_a_1689_);
v_isInstance_1731_ = lean_ctor_get_uint8(v___x_1730_, sizeof(void*)*1 + 4);
if (v_isInstance_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___f_1735_; 
lean_inc(v___x_1723_);
v___x_1732_ = lean_box(v_usedLetOnly_1686_);
v___x_1733_ = lean_box(v_skipConstInApp_1687_);
v___x_1734_ = lean_box(v_skipInstances_1688_);
lean_inc(v_a_1689_);
lean_inc(v___y_1691_);
lean_inc_ref(v_post_1685_);
lean_inc_ref(v_pre_1684_);
v___f_1735_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1735_, 0, v_pre_1684_);
lean_closure_set(v___f_1735_, 1, v_post_1685_);
lean_closure_set(v___f_1735_, 2, v___x_1732_);
lean_closure_set(v___f_1735_, 3, v___x_1733_);
lean_closure_set(v___f_1735_, 4, v___x_1734_);
lean_closure_set(v___f_1735_, 5, v___x_1723_);
lean_closure_set(v___f_1735_, 6, v___y_1691_);
lean_closure_set(v___f_1735_, 7, v_b_1690_);
lean_closure_set(v___f_1735_, 8, v_a_1689_);
v___y_1698_ = v___f_1735_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1736_; lean_object* v___f_1737_; 
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_b_1690_);
v___f_1737_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1737_, 0, v___x_1736_);
v___y_1698_ = v___f_1737_;
goto v___jp_1697_;
}
}
}
v___jp_1697_:
{
lean_object* v___x_1699_; 
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
lean_inc(v___y_1693_);
lean_inc_ref(v___y_1692_);
v___x_1699_ = lean_apply_5(v___y_1698_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, lean_box(0));
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1712_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1712_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1712_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
if (lean_obj_tag(v_a_1700_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; 
lean_dec(v_a_1689_);
lean_dec_ref(v_post_1685_);
lean_dec_ref(v_pre_1684_);
v_a_1704_ = lean_ctor_get(v_a_1700_, 0);
lean_inc(v_a_1704_);
lean_dec_ref(v_a_1700_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v_a_1704_);
v___x_1706_ = v___x_1702_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_del_object(v___x_1702_);
v_a_1708_ = lean_ctor_get(v_a_1700_, 0);
lean_inc(v_a_1708_);
lean_dec_ref(v_a_1700_);
v___x_1709_ = lean_unsigned_to_nat(1u);
v___x_1710_ = lean_nat_add(v_a_1689_, v___x_1709_);
lean_dec(v_a_1689_);
v_a_1689_ = v___x_1710_;
v_b_1690_ = v_a_1708_;
goto _start;
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_a_1689_);
lean_dec_ref(v_post_1685_);
lean_dec_ref(v_pre_1684_);
v_a_1713_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1699_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1699_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__16(uint8_t v_skipInstances_1738_, lean_object* v_pre_1739_, lean_object* v_post_1740_, uint8_t v_usedLetOnly_1741_, uint8_t v_skipConstInApp_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_, lean_object* v_x_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_f_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; 
if (lean_obj_tag(v_x_1743_) == 5)
{
lean_object* v_fn_1801_; lean_object* v_arg_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_fn_1801_ = lean_ctor_get(v_x_1743_, 0);
lean_inc_ref(v_fn_1801_);
v_arg_1802_ = lean_ctor_get(v_x_1743_, 1);
lean_inc_ref(v_arg_1802_);
lean_dec_ref(v_x_1743_);
v___x_1803_ = lean_array_set(v_x_1744_, v_x_1745_, v_arg_1802_);
v___x_1804_ = lean_unsigned_to_nat(1u);
v___x_1805_ = lean_nat_sub(v_x_1745_, v___x_1804_);
lean_dec(v_x_1745_);
v_x_1743_ = v_fn_1801_;
v_x_1744_ = v___x_1803_;
v_x_1745_ = v___x_1805_;
goto _start;
}
else
{
lean_dec(v_x_1745_);
if (v_skipConstInApp_1742_ == 0)
{
goto v___jp_1798_;
}
else
{
uint8_t v___x_1807_; 
v___x_1807_ = l_Lean_Expr_isConst(v_x_1743_);
if (v___x_1807_ == 0)
{
goto v___jp_1798_;
}
else
{
v_f_1753_ = v_x_1743_;
v___y_1754_ = v___y_1746_;
v___y_1755_ = v___y_1747_;
v___y_1756_ = v___y_1748_;
v___y_1757_ = v___y_1749_;
v___y_1758_ = v___y_1750_;
goto v___jp_1752_;
}
}
}
v___jp_1752_:
{
if (v_skipInstances_1738_ == 0)
{
size_t v_sz_1759_; size_t v___x_1760_; lean_object* v___x_1761_; 
v_sz_1759_ = lean_array_size(v_x_1744_);
v___x_1760_ = ((size_t)0ULL);
lean_inc_ref(v_post_1740_);
lean_inc_ref(v_pre_1739_);
v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__9(v_pre_1739_, v_post_1740_, v_usedLetOnly_1741_, v_skipConstInApp_1742_, v_skipInstances_1738_, v_sz_1759_, v___x_1760_, v_x_1744_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = l_Lean_mkAppN(v_f_1753_, v_a_1762_);
lean_dec(v_a_1762_);
v___x_1764_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1739_, v_post_1740_, v_usedLetOnly_1741_, v_skipConstInApp_1742_, v_skipInstances_1738_, v___x_1763_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
return v___x_1764_;
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v_f_1753_);
lean_dec_ref(v_post_1740_);
lean_dec_ref(v_pre_1739_);
v_a_1765_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1761_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1761_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_array_get_size(v_x_1744_);
lean_inc_ref(v_f_1753_);
v___x_1774_ = l_Lean_Meta_getFunInfoNArgs(v_f_1753_, v___x_1773_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v_paramInfo_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___x_1774_);
v_paramInfo_1776_ = lean_ctor_get(v_a_1775_, 0);
lean_inc_ref(v_paramInfo_1776_);
lean_dec(v_a_1775_);
v___x_1777_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1740_);
lean_inc_ref(v_pre_1739_);
v___x_1778_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg(v___x_1773_, v_paramInfo_1776_, v_pre_1739_, v_post_1740_, v_usedLetOnly_1741_, v_skipConstInApp_1742_, v_skipInstances_1738_, v___x_1777_, v_x_1744_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec_ref(v_paramInfo_1776_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref(v___x_1778_);
v___x_1780_ = l_Lean_mkAppN(v_f_1753_, v_a_1779_);
lean_dec(v_a_1779_);
v___x_1781_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1739_, v_post_1740_, v_usedLetOnly_1741_, v_skipConstInApp_1742_, v_skipInstances_1738_, v___x_1780_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
return v___x_1781_;
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v_f_1753_);
lean_dec_ref(v_post_1740_);
lean_dec_ref(v_pre_1739_);
v_a_1782_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1778_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1778_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v_f_1753_);
lean_dec_ref(v_x_1744_);
lean_dec_ref(v_post_1740_);
lean_dec_ref(v_pre_1739_);
v_a_1790_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1774_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1774_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
v___jp_1798_:
{
lean_object* v___x_1799_; 
lean_inc_ref(v_post_1740_);
lean_inc_ref(v_pre_1739_);
v___x_1799_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1739_, v_post_1740_, v_usedLetOnly_1741_, v_skipConstInApp_1742_, v_skipInstances_1738_, v_x_1743_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref(v___x_1799_);
v_f_1753_ = v_a_1800_;
v___y_1754_ = v___y_1746_;
v___y_1755_ = v___y_1747_;
v___y_1756_ = v___y_1748_;
v___y_1757_ = v___y_1749_;
v___y_1758_ = v___y_1750_;
goto v___jp_1752_;
}
else
{
lean_dec_ref(v_x_1744_);
lean_dec_ref(v_post_1740_);
lean_dec_ref(v_pre_1739_);
return v___x_1799_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1(lean_object* v___x_1808_, lean_object* v_pre_1809_, lean_object* v_e_1810_, lean_object* v_post_1811_, uint8_t v_usedLetOnly_1812_, uint8_t v_skipConstInApp_1813_, uint8_t v_skipInstances_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_Core_checkSystem(v___x_1808_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v___x_1822_; 
lean_dec_ref(v___x_1821_);
lean_inc_ref(v_pre_1809_);
lean_inc(v___y_1819_);
lean_inc_ref(v___y_1818_);
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1816_);
lean_inc_ref(v_e_1810_);
v___x_1822_ = lean_apply_6(v_pre_1809_, v_e_1810_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, lean_box(0));
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1871_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1871_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1871_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___y_1828_; 
switch(lean_obj_tag(v_a_1823_))
{
case 0:
{
lean_object* v_e_1863_; lean_object* v___x_1865_; 
lean_dec_ref(v_post_1811_);
lean_dec_ref(v_e_1810_);
lean_dec_ref(v_pre_1809_);
v_e_1863_ = lean_ctor_get(v_a_1823_, 0);
lean_inc_ref(v_e_1863_);
lean_dec_ref(v_a_1823_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v_e_1863_);
v___x_1865_ = v___x_1825_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_e_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
case 1:
{
lean_object* v_e_1867_; lean_object* v___x_1868_; 
lean_del_object(v___x_1825_);
lean_dec_ref(v_e_1810_);
v_e_1867_ = lean_ctor_get(v_a_1823_, 0);
lean_inc_ref(v_e_1867_);
lean_dec_ref(v_a_1823_);
v___x_1868_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1809_, v_post_1811_, v_usedLetOnly_1812_, v_skipConstInApp_1813_, v_skipInstances_1814_, v_e_1867_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1868_;
}
default: 
{
lean_object* v_e_x3f_1869_; 
lean_del_object(v___x_1825_);
v_e_x3f_1869_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_e_x3f_1869_);
lean_dec_ref(v_a_1823_);
if (lean_obj_tag(v_e_x3f_1869_) == 0)
{
v___y_1828_ = v_e_1810_;
goto v___jp_1827_;
}
else
{
lean_object* v_val_1870_; 
lean_dec_ref(v_e_1810_);
v_val_1870_ = lean_ctor_get(v_e_x3f_1869_, 0);
lean_inc(v_val_1870_);
lean_dec_ref(v_e_x3f_1869_);
v___y_1828_ = v_val_1870_;
goto v___jp_1827_;
}
}
}
v___jp_1827_:
{
switch(lean_obj_tag(v___y_1828_))
{
case 7:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__0));
v___x_1830_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13(v_pre_1809_, v_post_1811_, v_usedLetOnly_1812_, v_skipConstInApp_1813_, v_skipInstances_1814_, v___x_1829_, v___y_1828_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1830_;
}
case 6:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__0));
v___x_1832_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14(v_pre_1809_, v_post_1811_, v_usedLetOnly_1812_, v_skipConstInApp_1813_, v_skipInstances_1814_, v___x_1831_, v___y_1828_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1832_;
}
case 8:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__0));
v___x_1834_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15(v_pre_1809_, v_post_1811_, v_usedLetOnly_1812_, v_skipConstInApp_1813_, v_skipInstances_1814_, v___x_1833_, v___y_1828_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1834_;
}
case 5:
{
lean_object* v_dummy_1835_; lean_object* v_nargs_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v_dummy_1835_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1);
v_nargs_1836_ = l_Lean_Expr_getAppNumArgs(v___y_1828_);
lean_inc(v_nargs_1836_);
v___x_1837_ = lean_mk_array(v_nargs_1836_, v_dummy_1835_);
v___x_1838_ = lean_unsigned_to_nat(1u);
v___x_1839_ = lean_nat_sub(v_nargs_1836_, v___x_1838_);
lean_dec(v_nargs_1836_);
v___x_1840_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__16(v_skipInstances_1814_, v_pre_1809_, v_post_1811_, v_usedLetOnly_1812_, v_skipConstInApp_1813_, v___y_1828_, v___x_1837_, v___x_1839_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1840_;
}
case 10:
{
lean_object* v_data_1841_; lean_object* v_expr_1842_; lean_object* v___x_1843_; 
v_data_1841_ = lean_ctor_get(v___y_1828_, 0);
v_expr_1842_ = lean_ctor_get(v___y_1828_, 1);
lean_inc_ref(v_expr_1842_);
lean_inc_ref(v_post_1811_);
lean_inc_ref(v_pre_1809_);
v___x_1843_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1809_, v_post_1811_, v_usedLetOnly_1812_, v_skipConstInApp_1813_, v_skipInstances_1814_, v_expr_1842_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; size_t v___x_1845_; size_t v___x_1846_; uint8_t v___x_1847_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = lean_ptr_addr(v_expr_1842_);
v___x_1846_ = lean_ptr_addr(v_a_1844_);
v___x_1847_ = lean_usize_dec_eq(v___x_1845_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_inc(v_data_1841_);
lean_dec_ref(v___y_1828_);
v___x_1848_ = l_Lean_Expr_mdata___override(v_data_1841_, v_a_1844_);
v___x_1849_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1809_, v_post_1811_, v_usedLetOnly_1812_, v_skipConstInApp_1813_, v_skipInstances_1814_, v___x_1848_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; 
lean_dec(v_a_1844_);
v___x_1850_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1809_, v_post_1811_, v_usedLetOnly_1812_, v_skipConstInApp_1813_, v_skipInstances_1814_, v___y_1828_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1850_;
}
}
else
{
lean_dec_ref(v___y_1828_);
lean_dec_ref(v_post_1811_);
lean_dec_ref(v_pre_1809_);
return v___x_1843_;
}
}
case 11:
{
lean_object* v_typeName_1851_; lean_object* v_idx_1852_; lean_object* v_struct_1853_; lean_object* v___x_1854_; 
v_typeName_1851_ = lean_ctor_get(v___y_1828_, 0);
v_idx_1852_ = lean_ctor_get(v___y_1828_, 1);
v_struct_1853_ = lean_ctor_get(v___y_1828_, 2);
lean_inc_ref(v_struct_1853_);
lean_inc_ref(v_post_1811_);
lean_inc_ref(v_pre_1809_);
v___x_1854_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1809_, v_post_1811_, v_usedLetOnly_1812_, v_skipConstInApp_1813_, v_skipInstances_1814_, v_struct_1853_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; size_t v___x_1856_; size_t v___x_1857_; uint8_t v___x_1858_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref(v___x_1854_);
v___x_1856_ = lean_ptr_addr(v_struct_1853_);
v___x_1857_ = lean_ptr_addr(v_a_1855_);
v___x_1858_ = lean_usize_dec_eq(v___x_1856_, v___x_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_inc(v_idx_1852_);
lean_inc(v_typeName_1851_);
lean_dec_ref(v___y_1828_);
v___x_1859_ = l_Lean_Expr_proj___override(v_typeName_1851_, v_idx_1852_, v_a_1855_);
v___x_1860_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1809_, v_post_1811_, v_usedLetOnly_1812_, v_skipConstInApp_1813_, v_skipInstances_1814_, v___x_1859_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; 
lean_dec(v_a_1855_);
v___x_1861_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1809_, v_post_1811_, v_usedLetOnly_1812_, v_skipConstInApp_1813_, v_skipInstances_1814_, v___y_1828_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1861_;
}
}
else
{
lean_dec_ref(v___y_1828_);
lean_dec_ref(v_post_1811_);
lean_dec_ref(v_pre_1809_);
return v___x_1854_;
}
}
default: 
{
lean_object* v___x_1862_; 
v___x_1862_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1809_, v_post_1811_, v_usedLetOnly_1812_, v_skipConstInApp_1813_, v_skipInstances_1814_, v___y_1828_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1862_;
}
}
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v_post_1811_);
lean_dec_ref(v_e_1810_);
lean_dec_ref(v_pre_1809_);
v_a_1872_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1822_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1822_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v_post_1811_);
lean_dec_ref(v_e_1810_);
lean_dec_ref(v_pre_1809_);
v_a_1880_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1821_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1821_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___boxed(lean_object* v___x_1888_, lean_object* v_pre_1889_, lean_object* v_e_1890_, lean_object* v_post_1891_, lean_object* v_usedLetOnly_1892_, lean_object* v_skipConstInApp_1893_, lean_object* v_skipInstances_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
uint8_t v_usedLetOnly_boxed_1901_; uint8_t v_skipConstInApp_boxed_1902_; uint8_t v_skipInstances_boxed_1903_; lean_object* v_res_1904_; 
v_usedLetOnly_boxed_1901_ = lean_unbox(v_usedLetOnly_1892_);
v_skipConstInApp_boxed_1902_ = lean_unbox(v_skipConstInApp_1893_);
v_skipInstances_boxed_1903_ = lean_unbox(v_skipInstances_1894_);
v_res_1904_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1(v___x_1888_, v_pre_1889_, v_e_1890_, v_post_1891_, v_usedLetOnly_boxed_1901_, v_skipConstInApp_boxed_1902_, v_skipInstances_boxed_1903_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(lean_object* v_pre_1905_, lean_object* v_post_1906_, uint8_t v_usedLetOnly_1907_, uint8_t v_skipConstInApp_1908_, uint8_t v_skipInstances_1909_, lean_object* v_e_1910_, lean_object* v_a_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_inc(v_a_1911_);
v___x_1917_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1917_, 0, lean_box(0));
lean_closure_set(v___x_1917_, 1, lean_box(0));
lean_closure_set(v___x_1917_, 2, v_a_1911_);
v___x_1918_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__0(lean_box(0), v___x_1917_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1953_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1953_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1953_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12___redArg(v_a_1919_, v_e_1910_);
lean_dec(v_a_1919_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___f_1928_; lean_object* v___x_1929_; 
lean_del_object(v___x_1921_);
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___closed__0));
v___x_1925_ = lean_box(v_usedLetOnly_1907_);
v___x_1926_ = lean_box(v_skipConstInApp_1908_);
v___x_1927_ = lean_box(v_skipInstances_1909_);
lean_inc_ref(v_e_1910_);
v___f_1928_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1928_, 0, v___x_1924_);
lean_closure_set(v___f_1928_, 1, v_pre_1905_);
lean_closure_set(v___f_1928_, 2, v_e_1910_);
lean_closure_set(v___f_1928_, 3, v_post_1906_);
lean_closure_set(v___f_1928_, 4, v___x_1925_);
lean_closure_set(v___f_1928_, 5, v___x_1926_);
lean_closure_set(v___f_1928_, 6, v___x_1927_);
v___x_1929_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___redArg(v___f_1928_, v_a_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___f_1931_; lean_object* v___x_1932_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc_n(v_a_1930_, 2);
lean_dec_ref(v___x_1929_);
lean_inc(v_a_1911_);
v___f_1931_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1931_, 0, v_a_1911_);
lean_closure_set(v___f_1931_, 1, v_e_1910_);
lean_closure_set(v___f_1931_, 2, v_a_1930_);
v___x_1932_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__0(lean_box(0), v___f_1931_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1932_, 0);
lean_dec(v_unused_1940_);
v___x_1934_ = v___x_1932_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_dec(v___x_1932_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v_a_1930_);
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1930_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v_a_1930_);
v_a_1941_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1932_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1932_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_dec_ref(v_e_1910_);
return v___x_1929_;
}
}
else
{
lean_object* v_val_1949_; lean_object* v___x_1951_; 
lean_dec_ref(v_e_1910_);
lean_dec_ref(v_post_1906_);
lean_dec_ref(v_pre_1905_);
v_val_1949_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_val_1949_);
lean_dec_ref(v___x_1923_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v_val_1949_);
v___x_1951_ = v___x_1921_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_val_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec_ref(v_e_1910_);
lean_dec_ref(v_post_1906_);
lean_dec_ref(v_pre_1905_);
v_a_1954_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1918_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1918_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___lam__0___boxed(lean_object* v_fvars_1962_, lean_object* v_pre_1963_, lean_object* v_post_1964_, lean_object* v_usedLetOnly_1965_, lean_object* v_skipConstInApp_1966_, lean_object* v_skipInstances_1967_, lean_object* v_body_1968_, lean_object* v_x_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
uint8_t v_usedLetOnly_boxed_1976_; uint8_t v_skipConstInApp_boxed_1977_; uint8_t v_skipInstances_boxed_1978_; lean_object* v_res_1979_; 
v_usedLetOnly_boxed_1976_ = lean_unbox(v_usedLetOnly_1965_);
v_skipConstInApp_boxed_1977_ = lean_unbox(v_skipConstInApp_1966_);
v_skipInstances_boxed_1978_ = lean_unbox(v_skipInstances_1967_);
v_res_1979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___lam__0(v_fvars_1962_, v_pre_1963_, v_post_1964_, v_usedLetOnly_boxed_1976_, v_skipConstInApp_boxed_1977_, v_skipInstances_boxed_1978_, v_body_1968_, v_x_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13(lean_object* v_pre_1980_, lean_object* v_post_1981_, uint8_t v_usedLetOnly_1982_, uint8_t v_skipConstInApp_1983_, uint8_t v_skipInstances_1984_, lean_object* v_fvars_1985_, lean_object* v_e_1986_, lean_object* v_a_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
if (lean_obj_tag(v_e_1986_) == 7)
{
lean_object* v_binderName_1993_; lean_object* v_binderType_1994_; lean_object* v_body_1995_; uint8_t v_binderInfo_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_binderName_1993_ = lean_ctor_get(v_e_1986_, 0);
lean_inc(v_binderName_1993_);
v_binderType_1994_ = lean_ctor_get(v_e_1986_, 1);
lean_inc_ref(v_binderType_1994_);
v_body_1995_ = lean_ctor_get(v_e_1986_, 2);
lean_inc_ref(v_body_1995_);
v_binderInfo_1996_ = lean_ctor_get_uint8(v_e_1986_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1986_);
v___x_1997_ = lean_expr_instantiate_rev(v_binderType_1994_, v_fvars_1985_);
lean_dec_ref(v_binderType_1994_);
lean_inc_ref(v_post_1981_);
lean_inc_ref(v_pre_1980_);
v___x_1998_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1980_, v_post_1981_, v_usedLetOnly_1982_, v_skipConstInApp_1983_, v_skipInstances_1984_, v___x_1997_, v_a_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___f_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref(v___x_1998_);
v___x_2000_ = lean_box(v_usedLetOnly_1982_);
v___x_2001_ = lean_box(v_skipConstInApp_1983_);
v___x_2002_ = lean_box(v_skipInstances_1984_);
v___f_2003_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2003_, 0, v_fvars_1985_);
lean_closure_set(v___f_2003_, 1, v_pre_1980_);
lean_closure_set(v___f_2003_, 2, v_post_1981_);
lean_closure_set(v___f_2003_, 3, v___x_2000_);
lean_closure_set(v___f_2003_, 4, v___x_2001_);
lean_closure_set(v___f_2003_, 5, v___x_2002_);
lean_closure_set(v___f_2003_, 6, v_body_1995_);
v___x_2004_ = 0;
v___x_2005_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg(v_binderName_1993_, v_binderInfo_1996_, v_a_1999_, v___f_2003_, v___x_2004_, v_a_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
return v___x_2005_;
}
else
{
lean_dec_ref(v_body_1995_);
lean_dec(v_binderName_1993_);
lean_dec_ref(v_fvars_1985_);
lean_dec_ref(v_post_1981_);
lean_dec_ref(v_pre_1980_);
return v___x_1998_;
}
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_expr_instantiate_rev(v_e_1986_, v_fvars_1985_);
lean_dec_ref(v_e_1986_);
lean_inc_ref(v_post_1981_);
lean_inc_ref(v_pre_1980_);
v___x_2007_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1980_, v_post_1981_, v_usedLetOnly_1982_, v_skipConstInApp_1983_, v_skipInstances_1984_, v___x_2006_, v_a_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; uint8_t v___x_2009_; uint8_t v___x_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v___x_2007_);
v___x_2009_ = 0;
v___x_2010_ = 1;
v___x_2011_ = 1;
v___x_2012_ = l_Lean_Meta_mkForallFVars(v_fvars_1985_, v_a_2008_, v___x_2009_, v_usedLetOnly_1982_, v___x_2010_, v___x_2011_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec_ref(v_fvars_1985_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref(v___x_2012_);
v___x_2014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1980_, v_post_1981_, v_usedLetOnly_1982_, v_skipConstInApp_1983_, v_skipInstances_1984_, v_a_2013_, v_a_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
return v___x_2014_;
}
else
{
lean_dec_ref(v_post_1981_);
lean_dec_ref(v_pre_1980_);
return v___x_2012_;
}
}
else
{
lean_dec_ref(v_fvars_1985_);
lean_dec_ref(v_post_1981_);
lean_dec_ref(v_pre_1980_);
return v___x_2007_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___lam__0(lean_object* v_fvars_2015_, lean_object* v_pre_2016_, lean_object* v_post_2017_, uint8_t v_usedLetOnly_2018_, uint8_t v_skipConstInApp_2019_, uint8_t v_skipInstances_2020_, lean_object* v_body_2021_, lean_object* v_x_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_array_push(v_fvars_2015_, v_x_2022_);
v___x_2030_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13(v_pre_2016_, v_post_2017_, v_usedLetOnly_2018_, v_skipConstInApp_2019_, v_skipInstances_2020_, v___x_2029_, v_body_2021_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10___boxed(lean_object* v_pre_2031_, lean_object* v_post_2032_, lean_object* v_usedLetOnly_2033_, lean_object* v_skipConstInApp_2034_, lean_object* v_skipInstances_2035_, lean_object* v_e_2036_, lean_object* v_a_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
uint8_t v_usedLetOnly_boxed_2043_; uint8_t v_skipConstInApp_boxed_2044_; uint8_t v_skipInstances_boxed_2045_; lean_object* v_res_2046_; 
v_usedLetOnly_boxed_2043_ = lean_unbox(v_usedLetOnly_2033_);
v_skipConstInApp_boxed_2044_ = lean_unbox(v_skipConstInApp_2034_);
v_skipInstances_boxed_2045_ = lean_unbox(v_skipInstances_2035_);
v_res_2046_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_2031_, v_post_2032_, v_usedLetOnly_boxed_2043_, v_skipConstInApp_boxed_2044_, v_skipInstances_boxed_2045_, v_e_2036_, v_a_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v_a_2037_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__9___boxed(lean_object* v_pre_2047_, lean_object* v_post_2048_, lean_object* v_usedLetOnly_2049_, lean_object* v_skipConstInApp_2050_, lean_object* v_skipInstances_2051_, lean_object* v_sz_2052_, lean_object* v_i_2053_, lean_object* v_bs_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
uint8_t v_usedLetOnly_boxed_2061_; uint8_t v_skipConstInApp_boxed_2062_; uint8_t v_skipInstances_boxed_2063_; size_t v_sz_boxed_2064_; size_t v_i_boxed_2065_; lean_object* v_res_2066_; 
v_usedLetOnly_boxed_2061_ = lean_unbox(v_usedLetOnly_2049_);
v_skipConstInApp_boxed_2062_ = lean_unbox(v_skipConstInApp_2050_);
v_skipInstances_boxed_2063_ = lean_unbox(v_skipInstances_2051_);
v_sz_boxed_2064_ = lean_unbox_usize(v_sz_2052_);
lean_dec(v_sz_2052_);
v_i_boxed_2065_ = lean_unbox_usize(v_i_2053_);
lean_dec(v_i_2053_);
v_res_2066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__9(v_pre_2047_, v_post_2048_, v_usedLetOnly_boxed_2061_, v_skipConstInApp_boxed_2062_, v_skipInstances_boxed_2063_, v_sz_boxed_2064_, v_i_boxed_2065_, v_bs_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___boxed(lean_object* v_pre_2067_, lean_object* v_post_2068_, lean_object* v_usedLetOnly_2069_, lean_object* v_skipConstInApp_2070_, lean_object* v_skipInstances_2071_, lean_object* v_e_2072_, lean_object* v_a_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
uint8_t v_usedLetOnly_boxed_2079_; uint8_t v_skipConstInApp_boxed_2080_; uint8_t v_skipInstances_boxed_2081_; lean_object* v_res_2082_; 
v_usedLetOnly_boxed_2079_ = lean_unbox(v_usedLetOnly_2069_);
v_skipConstInApp_boxed_2080_ = lean_unbox(v_skipConstInApp_2070_);
v_skipInstances_boxed_2081_ = lean_unbox(v_skipInstances_2071_);
v_res_2082_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_2067_, v_post_2068_, v_usedLetOnly_boxed_2079_, v_skipConstInApp_boxed_2080_, v_skipInstances_boxed_2081_, v_e_2072_, v_a_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v_a_2073_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___boxed(lean_object* v_pre_2083_, lean_object* v_post_2084_, lean_object* v_usedLetOnly_2085_, lean_object* v_skipConstInApp_2086_, lean_object* v_skipInstances_2087_, lean_object* v_fvars_2088_, lean_object* v_e_2089_, lean_object* v_a_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
uint8_t v_usedLetOnly_boxed_2096_; uint8_t v_skipConstInApp_boxed_2097_; uint8_t v_skipInstances_boxed_2098_; lean_object* v_res_2099_; 
v_usedLetOnly_boxed_2096_ = lean_unbox(v_usedLetOnly_2085_);
v_skipConstInApp_boxed_2097_ = lean_unbox(v_skipConstInApp_2086_);
v_skipInstances_boxed_2098_ = lean_unbox(v_skipInstances_2087_);
v_res_2099_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13(v_pre_2083_, v_post_2084_, v_usedLetOnly_boxed_2096_, v_skipConstInApp_boxed_2097_, v_skipInstances_boxed_2098_, v_fvars_2088_, v_e_2089_, v_a_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v_a_2090_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___boxed(lean_object* v_pre_2100_, lean_object* v_post_2101_, lean_object* v_usedLetOnly_2102_, lean_object* v_skipConstInApp_2103_, lean_object* v_skipInstances_2104_, lean_object* v_fvars_2105_, lean_object* v_e_2106_, lean_object* v_a_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
uint8_t v_usedLetOnly_boxed_2113_; uint8_t v_skipConstInApp_boxed_2114_; uint8_t v_skipInstances_boxed_2115_; lean_object* v_res_2116_; 
v_usedLetOnly_boxed_2113_ = lean_unbox(v_usedLetOnly_2102_);
v_skipConstInApp_boxed_2114_ = lean_unbox(v_skipConstInApp_2103_);
v_skipInstances_boxed_2115_ = lean_unbox(v_skipInstances_2104_);
v_res_2116_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14(v_pre_2100_, v_post_2101_, v_usedLetOnly_boxed_2113_, v_skipConstInApp_boxed_2114_, v_skipInstances_boxed_2115_, v_fvars_2105_, v_e_2106_, v_a_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v_a_2107_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___boxed(lean_object* v_pre_2117_, lean_object* v_post_2118_, lean_object* v_usedLetOnly_2119_, lean_object* v_skipConstInApp_2120_, lean_object* v_skipInstances_2121_, lean_object* v_fvars_2122_, lean_object* v_e_2123_, lean_object* v_a_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
uint8_t v_usedLetOnly_boxed_2130_; uint8_t v_skipConstInApp_boxed_2131_; uint8_t v_skipInstances_boxed_2132_; lean_object* v_res_2133_; 
v_usedLetOnly_boxed_2130_ = lean_unbox(v_usedLetOnly_2119_);
v_skipConstInApp_boxed_2131_ = lean_unbox(v_skipConstInApp_2120_);
v_skipInstances_boxed_2132_ = lean_unbox(v_skipInstances_2121_);
v_res_2133_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15(v_pre_2117_, v_post_2118_, v_usedLetOnly_boxed_2130_, v_skipConstInApp_boxed_2131_, v_skipInstances_boxed_2132_, v_fvars_2122_, v_e_2123_, v_a_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v_a_2124_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_upperBound_2134_, lean_object* v___x_2135_, lean_object* v_pre_2136_, lean_object* v_post_2137_, lean_object* v_usedLetOnly_2138_, lean_object* v_skipConstInApp_2139_, lean_object* v_skipInstances_2140_, lean_object* v_a_2141_, lean_object* v_b_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
uint8_t v_usedLetOnly_boxed_2149_; uint8_t v_skipConstInApp_boxed_2150_; uint8_t v_skipInstances_boxed_2151_; lean_object* v_res_2152_; 
v_usedLetOnly_boxed_2149_ = lean_unbox(v_usedLetOnly_2138_);
v_skipConstInApp_boxed_2150_ = lean_unbox(v_skipConstInApp_2139_);
v_skipInstances_boxed_2151_ = lean_unbox(v_skipInstances_2140_);
v_res_2152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg(v_upperBound_2134_, v___x_2135_, v_pre_2136_, v_post_2137_, v_usedLetOnly_boxed_2149_, v_skipConstInApp_boxed_2150_, v_skipInstances_boxed_2151_, v_a_2141_, v_b_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___x_2135_);
lean_dec(v_upperBound_2134_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__16___boxed(lean_object* v_skipInstances_2153_, lean_object* v_pre_2154_, lean_object* v_post_2155_, lean_object* v_usedLetOnly_2156_, lean_object* v_skipConstInApp_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_, lean_object* v_x_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v_skipInstances_boxed_2167_; uint8_t v_usedLetOnly_boxed_2168_; uint8_t v_skipConstInApp_boxed_2169_; lean_object* v_res_2170_; 
v_skipInstances_boxed_2167_ = lean_unbox(v_skipInstances_2153_);
v_usedLetOnly_boxed_2168_ = lean_unbox(v_usedLetOnly_2156_);
v_skipConstInApp_boxed_2169_ = lean_unbox(v_skipConstInApp_2157_);
v_res_2170_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__16(v_skipInstances_boxed_2167_, v_pre_2154_, v_post_2155_, v_usedLetOnly_boxed_2168_, v_skipConstInApp_boxed_2169_, v_x_2158_, v_x_2159_, v_x_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
return v_res_2170_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2172_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2172_, 0, lean_box(0));
lean_closure_set(v___x_2172_, 1, lean_box(0));
lean_closure_set(v___x_2172_, 2, v___x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7(lean_object* v_input_2173_, lean_object* v_pre_2174_, lean_object* v_post_2175_, uint8_t v_usedLetOnly_2176_, uint8_t v_skipConstInApp_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v_a_2185_; uint8_t v___x_2186_; lean_object* v___x_2187_; 
v___x_2183_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0);
v___x_2184_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___lam__0(lean_box(0), v___x_2183_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref(v___x_2184_);
v___x_2186_ = 0;
v___x_2187_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_2174_, v_post_2175_, v_usedLetOnly_2176_, v_skipConstInApp_2177_, v___x_2186_, v_input_2173_, v_a_2185_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref(v___x_2187_);
v___x_2189_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2189_, 0, lean_box(0));
lean_closure_set(v___x_2189_, 1, lean_box(0));
lean_closure_set(v___x_2189_, 2, v_a_2185_);
v___x_2190_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___lam__0(lean_box(0), v___x_2189_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v___x_2190_, 0);
lean_dec(v_unused_2198_);
v___x_2192_ = v___x_2190_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_dec(v___x_2190_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_a_2188_);
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2188_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
else
{
lean_dec(v_a_2185_);
return v___x_2187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___boxed(lean_object* v_input_2199_, lean_object* v_pre_2200_, lean_object* v_post_2201_, lean_object* v_usedLetOnly_2202_, lean_object* v_skipConstInApp_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
uint8_t v_usedLetOnly_boxed_2209_; uint8_t v_skipConstInApp_boxed_2210_; lean_object* v_res_2211_; 
v_usedLetOnly_boxed_2209_ = lean_unbox(v_usedLetOnly_2202_);
v_skipConstInApp_boxed_2210_ = lean_unbox(v_skipConstInApp_2203_);
v_res_2211_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7(v_input_2199_, v_pre_2200_, v_post_2201_, v_usedLetOnly_boxed_2209_, v_skipConstInApp_boxed_2210_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
return v_res_2211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___lam__0(lean_object* v___x_2212_, lean_object* v_x_2213_){
_start:
{
lean_object* v_declName_2214_; uint8_t v___x_2215_; 
v_declName_2214_ = lean_ctor_get(v_x_2213_, 3);
v___x_2215_ = lean_name_eq(v_declName_2214_, v___x_2212_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___lam__0___boxed(lean_object* v___x_2216_, lean_object* v_x_2217_){
_start:
{
uint8_t v_res_2218_; lean_object* v_r_2219_; 
v_res_2218_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___lam__0(v___x_2216_, v_x_2217_);
lean_dec_ref(v_x_2217_);
lean_dec(v___x_2216_);
v_r_2219_ = lean_box(v_res_2218_);
return v_r_2219_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__0(lean_object* v_val_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_st_ref_get(v_val_2220_);
v___x_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__0___boxed(lean_object* v_val_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__0(v_val_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v_val_2228_);
return v_res_2234_;
}
}
static uint64_t _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0(void){
_start:
{
uint8_t v___x_2235_; uint64_t v___x_2236_; 
v___x_2235_ = 2;
v___x_2236_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg(lean_object* v_upperBound_2237_, lean_object* v_val_2238_, lean_object* v_next_2239_, lean_object* v_params_2240_, lean_object* v___x_2241_, lean_object* v_val_2242_, lean_object* v_next_2243_, uint8_t v___x_2244_, lean_object* v_a_2245_, uint8_t v_b_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
uint8_t v_a_2253_; uint8_t v___x_2257_; 
v___x_2257_ = lean_nat_dec_lt(v_a_2245_, v_upperBound_2237_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
lean_dec(v_a_2245_);
lean_dec(v_next_2243_);
lean_dec_ref(v___x_2241_);
v___x_2258_ = lean_box(v_b_2246_);
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
return v___x_2259_;
}
else
{
lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2260_ = lean_st_ref_get(v_val_2238_);
v___x_2261_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2239_, v_a_2245_, v___x_2260_);
lean_dec(v___x_2260_);
if (v___x_2261_ == 0)
{
v_a_2253_ = v_b_2246_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2262_; uint8_t v_foApprox_2263_; uint8_t v_ctxApprox_2264_; uint8_t v_quasiPatternApprox_2265_; uint8_t v_constApprox_2266_; uint8_t v_isDefEqStuckEx_2267_; uint8_t v_unificationHints_2268_; uint8_t v_assignSyntheticOpaque_2269_; uint8_t v_offsetCnstrs_2270_; uint8_t v_transparency_2271_; uint8_t v_etaStruct_2272_; uint8_t v_univApprox_2273_; uint8_t v_iota_2274_; uint8_t v_beta_2275_; uint8_t v_proj_2276_; uint8_t v_zeta_2277_; uint8_t v_zetaDelta_2278_; uint8_t v_zetaUnused_2279_; uint8_t v_zetaHave_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2343_; 
v___x_2262_ = l_Lean_Meta_Context_config(v___y_2247_);
v_foApprox_2263_ = lean_ctor_get_uint8(v___x_2262_, 0);
v_ctxApprox_2264_ = lean_ctor_get_uint8(v___x_2262_, 1);
v_quasiPatternApprox_2265_ = lean_ctor_get_uint8(v___x_2262_, 2);
v_constApprox_2266_ = lean_ctor_get_uint8(v___x_2262_, 3);
v_isDefEqStuckEx_2267_ = lean_ctor_get_uint8(v___x_2262_, 4);
v_unificationHints_2268_ = lean_ctor_get_uint8(v___x_2262_, 5);
v_assignSyntheticOpaque_2269_ = lean_ctor_get_uint8(v___x_2262_, 7);
v_offsetCnstrs_2270_ = lean_ctor_get_uint8(v___x_2262_, 8);
v_transparency_2271_ = lean_ctor_get_uint8(v___x_2262_, 9);
v_etaStruct_2272_ = lean_ctor_get_uint8(v___x_2262_, 10);
v_univApprox_2273_ = lean_ctor_get_uint8(v___x_2262_, 11);
v_iota_2274_ = lean_ctor_get_uint8(v___x_2262_, 12);
v_beta_2275_ = lean_ctor_get_uint8(v___x_2262_, 13);
v_proj_2276_ = lean_ctor_get_uint8(v___x_2262_, 14);
v_zeta_2277_ = lean_ctor_get_uint8(v___x_2262_, 15);
v_zetaDelta_2278_ = lean_ctor_get_uint8(v___x_2262_, 16);
v_zetaUnused_2279_ = lean_ctor_get_uint8(v___x_2262_, 17);
v_zetaHave_2280_ = lean_ctor_get_uint8(v___x_2262_, 18);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2282_ = v___x_2262_;
v_isShared_2283_ = v_isSharedCheck_2343_;
goto v_resetjp_2281_;
}
else
{
lean_dec(v___x_2262_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2343_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
uint8_t v_trackZetaDelta_2284_; lean_object* v_zetaDeltaSet_2285_; lean_object* v_lctx_2286_; lean_object* v_localInstances_2287_; lean_object* v_defEqCtx_x3f_2288_; lean_object* v_synthPendingDepth_2289_; lean_object* v_canUnfold_x3f_2290_; uint8_t v_univApprox_2291_; uint8_t v_inTypeClassResolution_2292_; uint8_t v_cacheInferType_2293_; uint8_t v___x_2294_; lean_object* v___x_2296_; 
v_trackZetaDelta_2284_ = lean_ctor_get_uint8(v___y_2247_, sizeof(void*)*7);
v_zetaDeltaSet_2285_ = lean_ctor_get(v___y_2247_, 1);
v_lctx_2286_ = lean_ctor_get(v___y_2247_, 2);
v_localInstances_2287_ = lean_ctor_get(v___y_2247_, 3);
v_defEqCtx_x3f_2288_ = lean_ctor_get(v___y_2247_, 4);
v_synthPendingDepth_2289_ = lean_ctor_get(v___y_2247_, 5);
v_canUnfold_x3f_2290_ = lean_ctor_get(v___y_2247_, 6);
v_univApprox_2291_ = lean_ctor_get_uint8(v___y_2247_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2292_ = lean_ctor_get_uint8(v___y_2247_, sizeof(void*)*7 + 2);
v_cacheInferType_2293_ = lean_ctor_get_uint8(v___y_2247_, sizeof(void*)*7 + 3);
v___x_2294_ = 0;
if (v_isShared_2283_ == 0)
{
v___x_2296_ = v___x_2282_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 0, v_foApprox_2263_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 1, v_ctxApprox_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 2, v_quasiPatternApprox_2265_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 3, v_constApprox_2266_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 4, v_isDefEqStuckEx_2267_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 5, v_unificationHints_2268_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 7, v_assignSyntheticOpaque_2269_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 8, v_offsetCnstrs_2270_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 9, v_transparency_2271_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 10, v_etaStruct_2272_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 11, v_univApprox_2273_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 12, v_iota_2274_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 13, v_beta_2275_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 14, v_proj_2276_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 15, v_zeta_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 16, v_zetaDelta_2278_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 17, v_zetaUnused_2279_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 18, v_zetaHave_2280_);
v___x_2296_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
uint64_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v_foApprox_2301_; uint8_t v_ctxApprox_2302_; uint8_t v_quasiPatternApprox_2303_; uint8_t v_constApprox_2304_; uint8_t v_isDefEqStuckEx_2305_; uint8_t v_unificationHints_2306_; uint8_t v_proofIrrelevance_2307_; uint8_t v_assignSyntheticOpaque_2308_; uint8_t v_offsetCnstrs_2309_; uint8_t v_etaStruct_2310_; uint8_t v_univApprox_2311_; uint8_t v_iota_2312_; uint8_t v_beta_2313_; uint8_t v_proj_2314_; uint8_t v_zeta_2315_; uint8_t v_zetaDelta_2316_; uint8_t v_zetaUnused_2317_; uint8_t v_zetaHave_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2341_; 
lean_ctor_set_uint8(v___x_2296_, 6, v___x_2294_);
v___x_2297_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2296_);
v___x_2298_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2298_, 0, v___x_2296_);
lean_ctor_set_uint64(v___x_2298_, sizeof(void*)*1, v___x_2297_);
lean_inc(v_canUnfold_x3f_2290_);
lean_inc(v_synthPendingDepth_2289_);
lean_inc(v_defEqCtx_x3f_2288_);
lean_inc_ref(v_localInstances_2287_);
lean_inc_ref(v_lctx_2286_);
lean_inc(v_zetaDeltaSet_2285_);
v___x_2299_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v_zetaDeltaSet_2285_);
lean_ctor_set(v___x_2299_, 2, v_lctx_2286_);
lean_ctor_set(v___x_2299_, 3, v_localInstances_2287_);
lean_ctor_set(v___x_2299_, 4, v_defEqCtx_x3f_2288_);
lean_ctor_set(v___x_2299_, 5, v_synthPendingDepth_2289_);
lean_ctor_set(v___x_2299_, 6, v_canUnfold_x3f_2290_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*7, v_trackZetaDelta_2284_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*7 + 1, v_univApprox_2291_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2292_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*7 + 3, v_cacheInferType_2293_);
v___x_2300_ = l_Lean_Meta_Context_config(v___x_2299_);
v_foApprox_2301_ = lean_ctor_get_uint8(v___x_2300_, 0);
v_ctxApprox_2302_ = lean_ctor_get_uint8(v___x_2300_, 1);
v_quasiPatternApprox_2303_ = lean_ctor_get_uint8(v___x_2300_, 2);
v_constApprox_2304_ = lean_ctor_get_uint8(v___x_2300_, 3);
v_isDefEqStuckEx_2305_ = lean_ctor_get_uint8(v___x_2300_, 4);
v_unificationHints_2306_ = lean_ctor_get_uint8(v___x_2300_, 5);
v_proofIrrelevance_2307_ = lean_ctor_get_uint8(v___x_2300_, 6);
v_assignSyntheticOpaque_2308_ = lean_ctor_get_uint8(v___x_2300_, 7);
v_offsetCnstrs_2309_ = lean_ctor_get_uint8(v___x_2300_, 8);
v_etaStruct_2310_ = lean_ctor_get_uint8(v___x_2300_, 10);
v_univApprox_2311_ = lean_ctor_get_uint8(v___x_2300_, 11);
v_iota_2312_ = lean_ctor_get_uint8(v___x_2300_, 12);
v_beta_2313_ = lean_ctor_get_uint8(v___x_2300_, 13);
v_proj_2314_ = lean_ctor_get_uint8(v___x_2300_, 14);
v_zeta_2315_ = lean_ctor_get_uint8(v___x_2300_, 15);
v_zetaDelta_2316_ = lean_ctor_get_uint8(v___x_2300_, 16);
v_zetaUnused_2317_ = lean_ctor_get_uint8(v___x_2300_, 17);
v_zetaHave_2318_ = lean_ctor_get_uint8(v___x_2300_, 18);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2320_ = v___x_2300_;
v_isShared_2321_ = v_isSharedCheck_2341_;
goto v_resetjp_2319_;
}
else
{
lean_dec(v___x_2300_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2341_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; uint8_t v___x_2323_; lean_object* v_config_2325_; 
v___x_2322_ = lean_array_fget_borrowed(v_params_2240_, v_a_2245_);
v___x_2323_ = 2;
if (v_isShared_2321_ == 0)
{
v_config_2325_ = v___x_2320_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 0, v_foApprox_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 1, v_ctxApprox_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 2, v_quasiPatternApprox_2303_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 3, v_constApprox_2304_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 4, v_isDefEqStuckEx_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 5, v_unificationHints_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 6, v_proofIrrelevance_2307_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 7, v_assignSyntheticOpaque_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 8, v_offsetCnstrs_2309_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 10, v_etaStruct_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 11, v_univApprox_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 12, v_iota_2312_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 13, v_beta_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 14, v_proj_2314_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 15, v_zeta_2315_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 16, v_zetaDelta_2316_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 17, v_zetaUnused_2317_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, 18, v_zetaHave_2318_);
v_config_2325_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
uint64_t v___x_2326_; uint64_t v___x_2327_; uint64_t v___x_2328_; uint64_t v___x_2329_; uint64_t v___x_2330_; uint64_t v_key_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_ctor_set_uint8(v_config_2325_, 9, v___x_2323_);
v___x_2326_ = l_Lean_Meta_Context_configKey(v___x_2299_);
lean_dec_ref(v___x_2299_);
v___x_2327_ = 2ULL;
v___x_2328_ = lean_uint64_shift_right(v___x_2326_, v___x_2327_);
v___x_2329_ = lean_uint64_shift_left(v___x_2328_, v___x_2327_);
v___x_2330_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0);
v_key_2331_ = lean_uint64_lor(v___x_2329_, v___x_2330_);
v___x_2332_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2332_, 0, v_config_2325_);
lean_ctor_set_uint64(v___x_2332_, sizeof(void*)*1, v_key_2331_);
lean_inc(v_canUnfold_x3f_2290_);
lean_inc(v_synthPendingDepth_2289_);
lean_inc(v_defEqCtx_x3f_2288_);
lean_inc_ref(v_localInstances_2287_);
lean_inc_ref(v_lctx_2286_);
lean_inc(v_zetaDeltaSet_2285_);
v___x_2333_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v_zetaDeltaSet_2285_);
lean_ctor_set(v___x_2333_, 2, v_lctx_2286_);
lean_ctor_set(v___x_2333_, 3, v_localInstances_2287_);
lean_ctor_set(v___x_2333_, 4, v_defEqCtx_x3f_2288_);
lean_ctor_set(v___x_2333_, 5, v_synthPendingDepth_2289_);
lean_ctor_set(v___x_2333_, 6, v_canUnfold_x3f_2290_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*7, v_trackZetaDelta_2284_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*7 + 1, v_univApprox_2291_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2292_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*7 + 3, v_cacheInferType_2293_);
lean_inc_ref(v___x_2241_);
lean_inc(v___x_2322_);
v___x_2334_ = l_Lean_Meta_isExprDefEq(v___x_2322_, v___x_2241_, v___x_2333_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec_ref(v___x_2333_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; uint8_t v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref(v___x_2334_);
v___x_2336_ = lean_unbox(v_a_2335_);
lean_dec(v_a_2335_);
if (v___x_2336_ == 0)
{
v_a_2253_ = v_b_2246_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = lean_st_ref_take(v_val_2238_);
lean_inc(v_a_2245_);
lean_inc(v_next_2243_);
v___x_2338_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2242_, v_next_2243_, v_next_2239_, v_a_2245_, v___x_2337_);
v___x_2339_ = lean_st_ref_set(v_val_2238_, v___x_2338_);
v_a_2253_ = v___x_2244_;
goto v___jp_2252_;
}
}
else
{
lean_dec(v_a_2245_);
lean_dec(v_next_2243_);
lean_dec_ref(v___x_2241_);
return v___x_2334_;
}
}
}
}
}
}
}
v___jp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_unsigned_to_nat(1u);
v___x_2255_ = lean_nat_add(v_a_2245_, v___x_2254_);
lean_dec(v_a_2245_);
v_a_2245_ = v___x_2255_;
v_b_2246_ = v_a_2253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___boxed(lean_object* v_upperBound_2344_, lean_object* v_val_2345_, lean_object* v_next_2346_, lean_object* v_params_2347_, lean_object* v___x_2348_, lean_object* v_val_2349_, lean_object* v_next_2350_, lean_object* v___x_2351_, lean_object* v_a_2352_, lean_object* v_b_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
uint8_t v___x_44317__boxed_2359_; uint8_t v_b_boxed_2360_; lean_object* v_res_2361_; 
v___x_44317__boxed_2359_ = lean_unbox(v___x_2351_);
v_b_boxed_2360_ = lean_unbox(v_b_2353_);
v_res_2361_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg(v_upperBound_2344_, v_val_2345_, v_next_2346_, v_params_2347_, v___x_2348_, v_val_2349_, v_next_2350_, v___x_44317__boxed_2359_, v_a_2352_, v_b_boxed_2360_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v_val_2349_);
lean_dec_ref(v_params_2347_);
lean_dec(v_next_2346_);
lean_dec(v_val_2345_);
lean_dec(v_upperBound_2344_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(lean_object* v_msgData_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; lean_object* v_env_2369_; lean_object* v___x_2370_; lean_object* v_mctx_2371_; lean_object* v_lctx_2372_; lean_object* v_options_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2368_ = lean_st_ref_get(v___y_2366_);
v_env_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc_ref(v_env_2369_);
lean_dec(v___x_2368_);
v___x_2370_ = lean_st_ref_get(v___y_2364_);
v_mctx_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc_ref(v_mctx_2371_);
lean_dec(v___x_2370_);
v_lctx_2372_ = lean_ctor_get(v___y_2363_, 2);
v_options_2373_ = lean_ctor_get(v___y_2365_, 2);
lean_inc_ref(v_options_2373_);
lean_inc_ref(v_lctx_2372_);
v___x_2374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2374_, 0, v_env_2369_);
lean_ctor_set(v___x_2374_, 1, v_mctx_2371_);
lean_ctor_set(v___x_2374_, 2, v_lctx_2372_);
lean_ctor_set(v___x_2374_, 3, v_options_2373_);
v___x_2375_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set(v___x_2375_, 1, v_msgData_2362_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2___boxed(lean_object* v_msgData_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msgData_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
return v_res_2383_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2384_; double v___x_2385_; 
v___x_2384_ = lean_unsigned_to_nat(0u);
v___x_2385_ = lean_float_of_nat(v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(lean_object* v_cls_2389_, lean_object* v_msg_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_ref_2396_; lean_object* v___x_2397_; lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2442_; 
v_ref_2396_ = lean_ctor_get(v___y_2393_, 5);
v___x_2397_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msg_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2442_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2442_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v_traceState_2403_; lean_object* v_env_2404_; lean_object* v_nextMacroScope_2405_; lean_object* v_ngen_2406_; lean_object* v_auxDeclNGen_2407_; lean_object* v_cache_2408_; lean_object* v_messages_2409_; lean_object* v_infoState_2410_; lean_object* v_snapshotTasks_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2441_; 
v___x_2402_ = lean_st_ref_take(v___y_2394_);
v_traceState_2403_ = lean_ctor_get(v___x_2402_, 4);
v_env_2404_ = lean_ctor_get(v___x_2402_, 0);
v_nextMacroScope_2405_ = lean_ctor_get(v___x_2402_, 1);
v_ngen_2406_ = lean_ctor_get(v___x_2402_, 2);
v_auxDeclNGen_2407_ = lean_ctor_get(v___x_2402_, 3);
v_cache_2408_ = lean_ctor_get(v___x_2402_, 5);
v_messages_2409_ = lean_ctor_get(v___x_2402_, 6);
v_infoState_2410_ = lean_ctor_get(v___x_2402_, 7);
v_snapshotTasks_2411_ = lean_ctor_get(v___x_2402_, 8);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2413_ = v___x_2402_;
v_isShared_2414_ = v_isSharedCheck_2441_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_snapshotTasks_2411_);
lean_inc(v_infoState_2410_);
lean_inc(v_messages_2409_);
lean_inc(v_cache_2408_);
lean_inc(v_traceState_2403_);
lean_inc(v_auxDeclNGen_2407_);
lean_inc(v_ngen_2406_);
lean_inc(v_nextMacroScope_2405_);
lean_inc(v_env_2404_);
lean_dec(v___x_2402_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2441_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
uint64_t v_tid_2415_; lean_object* v_traces_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2440_; 
v_tid_2415_ = lean_ctor_get_uint64(v_traceState_2403_, sizeof(void*)*1);
v_traces_2416_ = lean_ctor_get(v_traceState_2403_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v_traceState_2403_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2418_ = v_traceState_2403_;
v_isShared_2419_ = v_isSharedCheck_2440_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_traces_2416_);
lean_dec(v_traceState_2403_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2440_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; double v___x_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
v___x_2420_ = lean_box(0);
v___x_2421_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0);
v___x_2422_ = 0;
v___x_2423_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1));
v___x_2424_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2424_, 0, v_cls_2389_);
lean_ctor_set(v___x_2424_, 1, v___x_2420_);
lean_ctor_set(v___x_2424_, 2, v___x_2423_);
lean_ctor_set_float(v___x_2424_, sizeof(void*)*3, v___x_2421_);
lean_ctor_set_float(v___x_2424_, sizeof(void*)*3 + 8, v___x_2421_);
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*3 + 16, v___x_2422_);
v___x_2425_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2));
v___x_2426_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
lean_ctor_set(v___x_2426_, 1, v_a_2398_);
lean_ctor_set(v___x_2426_, 2, v___x_2425_);
lean_inc(v_ref_2396_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v_ref_2396_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = l_Lean_PersistentArray_push___redArg(v_traces_2416_, v___x_2427_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2428_);
v___x_2430_ = v___x_2418_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2428_);
lean_ctor_set_uint64(v_reuseFailAlloc_2439_, sizeof(void*)*1, v_tid_2415_);
v___x_2430_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v___x_2432_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 4, v___x_2430_);
v___x_2432_ = v___x_2413_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_env_2404_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_nextMacroScope_2405_);
lean_ctor_set(v_reuseFailAlloc_2438_, 2, v_ngen_2406_);
lean_ctor_set(v_reuseFailAlloc_2438_, 3, v_auxDeclNGen_2407_);
lean_ctor_set(v_reuseFailAlloc_2438_, 4, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2438_, 5, v_cache_2408_);
lean_ctor_set(v_reuseFailAlloc_2438_, 6, v_messages_2409_);
lean_ctor_set(v_reuseFailAlloc_2438_, 7, v_infoState_2410_);
lean_ctor_set(v_reuseFailAlloc_2438_, 8, v_snapshotTasks_2411_);
v___x_2432_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2433_ = lean_st_ref_set(v___y_2394_, v___x_2432_);
v___x_2434_ = lean_box(0);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2434_);
v___x_2436_ = v___x_2400_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___boxed(lean_object* v_cls_2443_, lean_object* v_msg_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v_cls_2443_, v_msg_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(lean_object* v_val_2451_, lean_object* v_val_2452_, lean_object* v_a_2453_, lean_object* v___x_2454_, lean_object* v_____r_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2461_ = lean_st_ref_take(v_val_2451_);
v___x_2462_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2452_, v_a_2453_, v___x_2461_);
v___x_2463_ = lean_st_ref_set(v_val_2451_, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2454_);
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1___boxed(lean_object* v_val_2466_, lean_object* v_val_2467_, lean_object* v_a_2468_, lean_object* v___x_2469_, lean_object* v_____r_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2466_, v_val_2467_, v_a_2468_, v___x_2469_, v_____r_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v_val_2467_);
lean_dec(v_val_2466_);
return v_res_2476_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3));
v___x_2488_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__5));
v___x_2489_ = l_Lean_Name_append(v___x_2488_, v___x_2487_);
return v___x_2489_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__7));
v___x_2492_ = l_Lean_stringToMessageData(v___x_2491_);
return v___x_2492_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2494_ = l_Lean_stringToMessageData(v___x_2493_);
return v___x_2494_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__10));
v___x_2497_ = l_Lean_stringToMessageData(v___x_2496_);
return v___x_2497_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__12));
v___x_2500_ = l_Lean_stringToMessageData(v___x_2499_);
return v___x_2500_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__14));
v___x_2503_ = l_Lean_stringToMessageData(v___x_2502_);
return v___x_2503_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__16));
v___x_2506_ = l_Lean_stringToMessageData(v___x_2505_);
return v___x_2506_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__18));
v___x_2509_ = l_Lean_stringToMessageData(v___x_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_val_2510_, lean_object* v_val_2511_, lean_object* v_upperBound_2512_, lean_object* v_args_2513_, lean_object* v_e_2514_, lean_object* v_next_2515_, lean_object* v_params_2516_, lean_object* v___x_2517_, uint8_t v___x_2518_, lean_object* v_a_2519_, lean_object* v_b_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_a_2527_; lean_object* v___y_2532_; uint8_t v___x_2551_; 
v___x_2551_ = lean_nat_dec_lt(v_a_2519_, v_upperBound_2512_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; 
lean_dec(v_a_2519_);
lean_dec_ref(v_e_2514_);
lean_dec(v_val_2511_);
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v_b_2520_);
return v___x_2552_;
}
else
{
lean_object* v___x_2553_; 
v___x_2553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__0(v_val_2510_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref(v___x_2553_);
v___x_2555_ = lean_box(0);
v___x_2556_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2511_, v_a_2519_, v_a_2554_);
lean_dec(v_a_2554_);
if (v___x_2556_ == 0)
{
v_a_2527_ = v___x_2555_;
goto v___jp_2526_;
}
else
{
lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2557_ = lean_array_get_size(v_args_2513_);
v___x_2558_ = lean_nat_dec_lt(v_a_2519_, v___x_2557_);
if (v___x_2558_ == 0)
{
lean_object* v_options_2559_; lean_object* v_inheritedTraceOptions_2560_; uint8_t v_hasTrace_2561_; 
v_options_2559_ = lean_ctor_get(v___y_2523_, 2);
v_inheritedTraceOptions_2560_ = lean_ctor_get(v___y_2523_, 13);
v_hasTrace_2561_ = lean_ctor_get_uint8(v_options_2559_, sizeof(void*)*1);
if (v_hasTrace_2561_ == 0)
{
goto v___jp_2562_;
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v___x_2564_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3));
v___x_2565_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6);
v___x_2566_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2560_, v_options_2559_, v___x_2565_);
if (v___x_2566_ == 0)
{
goto v___jp_2562_;
}
else
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2567_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8);
lean_inc(v_val_2511_);
v___x_2568_ = l_Nat_reprFast(v_val_2511_);
v___x_2569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
v___x_2570_ = l_Lean_MessageData_ofFormat(v___x_2569_);
v___x_2571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2567_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9);
v___x_2573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
lean_inc(v_a_2519_);
v___x_2574_ = l_Nat_reprFast(v_a_2519_);
v___x_2575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
v___x_2576_ = l_Lean_MessageData_ofFormat(v___x_2575_);
lean_inc_ref(v___x_2576_);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2573_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
lean_inc_ref(v_e_2514_);
v___x_2580_ = l_Lean_MessageData_ofExpr(v_e_2514_);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__13);
v___x_2583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___x_2576_);
v___x_2585_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2564_, v___x_2584_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2587_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref(v___x_2585_);
lean_inc(v_a_2519_);
v___x_2587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2510_, v_val_2511_, v_a_2519_, v___x_2555_, v_a_2586_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
v___y_2532_ = v___x_2587_;
goto v___jp_2531_;
}
else
{
lean_dec(v_a_2519_);
lean_dec_ref(v_e_2514_);
lean_dec(v_val_2511_);
return v___x_2585_;
}
}
}
v___jp_2562_:
{
lean_object* v___x_2563_; 
lean_inc(v_a_2519_);
v___x_2563_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2510_, v_val_2511_, v_a_2519_, v___x_2555_, v___x_2555_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
v___y_2532_ = v___x_2563_;
goto v___jp_2531_;
}
}
else
{
lean_object* v___x_2588_; 
v___x_2588_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__0(v_val_2510_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref(v___x_2588_);
v___x_2590_ = lean_array_fget_borrowed(v_args_2513_, v_a_2519_);
v___x_2591_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2511_, v_a_2519_, v_next_2515_, v_a_2589_);
lean_dec(v_a_2589_);
if (lean_obj_tag(v___x_2591_) == 1)
{
lean_object* v_val_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2720_; 
v_val_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2720_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_val_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2720_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; uint8_t v_foApprox_2597_; uint8_t v_ctxApprox_2598_; uint8_t v_quasiPatternApprox_2599_; uint8_t v_constApprox_2600_; uint8_t v_isDefEqStuckEx_2601_; uint8_t v_unificationHints_2602_; uint8_t v_assignSyntheticOpaque_2603_; uint8_t v_offsetCnstrs_2604_; uint8_t v_transparency_2605_; uint8_t v_etaStruct_2606_; uint8_t v_univApprox_2607_; uint8_t v_iota_2608_; uint8_t v_beta_2609_; uint8_t v_proj_2610_; uint8_t v_zeta_2611_; uint8_t v_zetaDelta_2612_; uint8_t v_zetaUnused_2613_; uint8_t v_zetaHave_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2719_; 
v___x_2596_ = l_Lean_Meta_Context_config(v___y_2521_);
v_foApprox_2597_ = lean_ctor_get_uint8(v___x_2596_, 0);
v_ctxApprox_2598_ = lean_ctor_get_uint8(v___x_2596_, 1);
v_quasiPatternApprox_2599_ = lean_ctor_get_uint8(v___x_2596_, 2);
v_constApprox_2600_ = lean_ctor_get_uint8(v___x_2596_, 3);
v_isDefEqStuckEx_2601_ = lean_ctor_get_uint8(v___x_2596_, 4);
v_unificationHints_2602_ = lean_ctor_get_uint8(v___x_2596_, 5);
v_assignSyntheticOpaque_2603_ = lean_ctor_get_uint8(v___x_2596_, 7);
v_offsetCnstrs_2604_ = lean_ctor_get_uint8(v___x_2596_, 8);
v_transparency_2605_ = lean_ctor_get_uint8(v___x_2596_, 9);
v_etaStruct_2606_ = lean_ctor_get_uint8(v___x_2596_, 10);
v_univApprox_2607_ = lean_ctor_get_uint8(v___x_2596_, 11);
v_iota_2608_ = lean_ctor_get_uint8(v___x_2596_, 12);
v_beta_2609_ = lean_ctor_get_uint8(v___x_2596_, 13);
v_proj_2610_ = lean_ctor_get_uint8(v___x_2596_, 14);
v_zeta_2611_ = lean_ctor_get_uint8(v___x_2596_, 15);
v_zetaDelta_2612_ = lean_ctor_get_uint8(v___x_2596_, 16);
v_zetaUnused_2613_ = lean_ctor_get_uint8(v___x_2596_, 17);
v_zetaHave_2614_ = lean_ctor_get_uint8(v___x_2596_, 18);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2616_ = v___x_2596_;
v_isShared_2617_ = v_isSharedCheck_2719_;
goto v_resetjp_2615_;
}
else
{
lean_dec(v___x_2596_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2719_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
uint8_t v_trackZetaDelta_2618_; lean_object* v_zetaDeltaSet_2619_; lean_object* v_lctx_2620_; lean_object* v_localInstances_2621_; lean_object* v_defEqCtx_x3f_2622_; lean_object* v_synthPendingDepth_2623_; lean_object* v_canUnfold_x3f_2624_; uint8_t v_univApprox_2625_; uint8_t v_inTypeClassResolution_2626_; uint8_t v_cacheInferType_2627_; uint8_t v___x_2628_; lean_object* v___x_2630_; 
v_trackZetaDelta_2618_ = lean_ctor_get_uint8(v___y_2521_, sizeof(void*)*7);
v_zetaDeltaSet_2619_ = lean_ctor_get(v___y_2521_, 1);
v_lctx_2620_ = lean_ctor_get(v___y_2521_, 2);
v_localInstances_2621_ = lean_ctor_get(v___y_2521_, 3);
v_defEqCtx_x3f_2622_ = lean_ctor_get(v___y_2521_, 4);
v_synthPendingDepth_2623_ = lean_ctor_get(v___y_2521_, 5);
v_canUnfold_x3f_2624_ = lean_ctor_get(v___y_2521_, 6);
v_univApprox_2625_ = lean_ctor_get_uint8(v___y_2521_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2626_ = lean_ctor_get_uint8(v___y_2521_, sizeof(void*)*7 + 2);
v_cacheInferType_2627_ = lean_ctor_get_uint8(v___y_2521_, sizeof(void*)*7 + 3);
v___x_2628_ = 0;
if (v_isShared_2617_ == 0)
{
v___x_2630_ = v___x_2616_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 0, v_foApprox_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 1, v_ctxApprox_2598_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 2, v_quasiPatternApprox_2599_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 3, v_constApprox_2600_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 4, v_isDefEqStuckEx_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 5, v_unificationHints_2602_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 7, v_assignSyntheticOpaque_2603_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 8, v_offsetCnstrs_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 9, v_transparency_2605_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 10, v_etaStruct_2606_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 11, v_univApprox_2607_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 12, v_iota_2608_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 13, v_beta_2609_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 14, v_proj_2610_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 15, v_zeta_2611_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 16, v_zetaDelta_2612_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 17, v_zetaUnused_2613_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, 18, v_zetaHave_2614_);
v___x_2630_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
uint64_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; uint8_t v_foApprox_2635_; uint8_t v_ctxApprox_2636_; uint8_t v_quasiPatternApprox_2637_; uint8_t v_constApprox_2638_; uint8_t v_isDefEqStuckEx_2639_; uint8_t v_unificationHints_2640_; uint8_t v_proofIrrelevance_2641_; uint8_t v_assignSyntheticOpaque_2642_; uint8_t v_offsetCnstrs_2643_; uint8_t v_etaStruct_2644_; uint8_t v_univApprox_2645_; uint8_t v_iota_2646_; uint8_t v_beta_2647_; uint8_t v_proj_2648_; uint8_t v_zeta_2649_; uint8_t v_zetaDelta_2650_; uint8_t v_zetaUnused_2651_; uint8_t v_zetaHave_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2717_; 
lean_ctor_set_uint8(v___x_2630_, 6, v___x_2628_);
v___x_2631_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2630_);
v___x_2632_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2632_, 0, v___x_2630_);
lean_ctor_set_uint64(v___x_2632_, sizeof(void*)*1, v___x_2631_);
lean_inc(v_canUnfold_x3f_2624_);
lean_inc(v_synthPendingDepth_2623_);
lean_inc(v_defEqCtx_x3f_2622_);
lean_inc_ref(v_localInstances_2621_);
lean_inc_ref(v_lctx_2620_);
lean_inc(v_zetaDeltaSet_2619_);
v___x_2633_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v_zetaDeltaSet_2619_);
lean_ctor_set(v___x_2633_, 2, v_lctx_2620_);
lean_ctor_set(v___x_2633_, 3, v_localInstances_2621_);
lean_ctor_set(v___x_2633_, 4, v_defEqCtx_x3f_2622_);
lean_ctor_set(v___x_2633_, 5, v_synthPendingDepth_2623_);
lean_ctor_set(v___x_2633_, 6, v_canUnfold_x3f_2624_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*7, v_trackZetaDelta_2618_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*7 + 1, v_univApprox_2625_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2626_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*7 + 3, v_cacheInferType_2627_);
v___x_2634_ = l_Lean_Meta_Context_config(v___x_2633_);
v_foApprox_2635_ = lean_ctor_get_uint8(v___x_2634_, 0);
v_ctxApprox_2636_ = lean_ctor_get_uint8(v___x_2634_, 1);
v_quasiPatternApprox_2637_ = lean_ctor_get_uint8(v___x_2634_, 2);
v_constApprox_2638_ = lean_ctor_get_uint8(v___x_2634_, 3);
v_isDefEqStuckEx_2639_ = lean_ctor_get_uint8(v___x_2634_, 4);
v_unificationHints_2640_ = lean_ctor_get_uint8(v___x_2634_, 5);
v_proofIrrelevance_2641_ = lean_ctor_get_uint8(v___x_2634_, 6);
v_assignSyntheticOpaque_2642_ = lean_ctor_get_uint8(v___x_2634_, 7);
v_offsetCnstrs_2643_ = lean_ctor_get_uint8(v___x_2634_, 8);
v_etaStruct_2644_ = lean_ctor_get_uint8(v___x_2634_, 10);
v_univApprox_2645_ = lean_ctor_get_uint8(v___x_2634_, 11);
v_iota_2646_ = lean_ctor_get_uint8(v___x_2634_, 12);
v_beta_2647_ = lean_ctor_get_uint8(v___x_2634_, 13);
v_proj_2648_ = lean_ctor_get_uint8(v___x_2634_, 14);
v_zeta_2649_ = lean_ctor_get_uint8(v___x_2634_, 15);
v_zetaDelta_2650_ = lean_ctor_get_uint8(v___x_2634_, 16);
v_zetaUnused_2651_ = lean_ctor_get_uint8(v___x_2634_, 17);
v_zetaHave_2652_ = lean_ctor_get_uint8(v___x_2634_, 18);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2654_ = v___x_2634_;
v_isShared_2655_ = v_isSharedCheck_2717_;
goto v_resetjp_2653_;
}
else
{
lean_dec(v___x_2634_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2717_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; lean_object* v_config_2660_; 
v___x_2656_ = l_Lean_instInhabitedExpr;
v___x_2657_ = lean_array_get_borrowed(v___x_2656_, v_params_2516_, v_val_2592_);
lean_dec(v_val_2592_);
v___x_2658_ = 2;
if (v_isShared_2655_ == 0)
{
v_config_2660_ = v___x_2654_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 0, v_foApprox_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 1, v_ctxApprox_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 2, v_quasiPatternApprox_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 3, v_constApprox_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 4, v_isDefEqStuckEx_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 5, v_unificationHints_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 6, v_proofIrrelevance_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 7, v_assignSyntheticOpaque_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 8, v_offsetCnstrs_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 10, v_etaStruct_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 11, v_univApprox_2645_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 12, v_iota_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 13, v_beta_2647_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 14, v_proj_2648_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 15, v_zeta_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 16, v_zetaDelta_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 17, v_zetaUnused_2651_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, 18, v_zetaHave_2652_);
v_config_2660_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
uint64_t v___x_2661_; uint64_t v___x_2662_; uint64_t v___x_2663_; uint64_t v___x_2664_; uint64_t v___x_2665_; uint64_t v_key_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_ctor_set_uint8(v_config_2660_, 9, v___x_2658_);
v___x_2661_ = l_Lean_Meta_Context_configKey(v___x_2633_);
lean_dec_ref(v___x_2633_);
v___x_2662_ = 2ULL;
v___x_2663_ = lean_uint64_shift_right(v___x_2661_, v___x_2662_);
v___x_2664_ = lean_uint64_shift_left(v___x_2663_, v___x_2662_);
v___x_2665_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0);
v_key_2666_ = lean_uint64_lor(v___x_2664_, v___x_2665_);
v___x_2667_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2667_, 0, v_config_2660_);
lean_ctor_set_uint64(v___x_2667_, sizeof(void*)*1, v_key_2666_);
lean_inc(v_canUnfold_x3f_2624_);
lean_inc(v_synthPendingDepth_2623_);
lean_inc(v_defEqCtx_x3f_2622_);
lean_inc_ref(v_localInstances_2621_);
lean_inc_ref(v_lctx_2620_);
lean_inc(v_zetaDeltaSet_2619_);
v___x_2668_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
lean_ctor_set(v___x_2668_, 1, v_zetaDeltaSet_2619_);
lean_ctor_set(v___x_2668_, 2, v_lctx_2620_);
lean_ctor_set(v___x_2668_, 3, v_localInstances_2621_);
lean_ctor_set(v___x_2668_, 4, v_defEqCtx_x3f_2622_);
lean_ctor_set(v___x_2668_, 5, v_synthPendingDepth_2623_);
lean_ctor_set(v___x_2668_, 6, v_canUnfold_x3f_2624_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*7, v_trackZetaDelta_2618_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*7 + 1, v_univApprox_2625_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2626_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*7 + 3, v_cacheInferType_2627_);
lean_inc(v___x_2590_);
lean_inc(v___x_2657_);
v___x_2669_ = l_Lean_Meta_isExprDefEq(v___x_2657_, v___x_2590_, v___x_2668_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec_ref(v___x_2668_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; uint8_t v___x_2671_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref(v___x_2669_);
v___x_2671_ = lean_unbox(v_a_2670_);
lean_dec(v_a_2670_);
if (v___x_2671_ == 0)
{
lean_object* v_options_2672_; lean_object* v_inheritedTraceOptions_2673_; uint8_t v_hasTrace_2674_; 
v_options_2672_ = lean_ctor_get(v___y_2523_, 2);
v_inheritedTraceOptions_2673_ = lean_ctor_get(v___y_2523_, 13);
v_hasTrace_2674_ = lean_ctor_get_uint8(v_options_2672_, sizeof(void*)*1);
if (v_hasTrace_2674_ == 0)
{
lean_del_object(v___x_2594_);
goto v___jp_2675_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v___x_2677_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3));
v___x_2678_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6);
v___x_2679_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2673_, v_options_2672_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_del_object(v___x_2594_);
goto v___jp_2675_;
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2680_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8);
lean_inc(v_val_2511_);
v___x_2681_ = l_Nat_reprFast(v_val_2511_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set_tag(v___x_2594_, 3);
lean_ctor_set(v___x_2594_, 0, v___x_2681_);
v___x_2683_ = v___x_2594_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2684_ = l_Lean_MessageData_ofFormat(v___x_2683_);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2680_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
lean_inc(v_a_2519_);
v___x_2688_ = l_Nat_reprFast(v_a_2519_);
v___x_2689_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
v___x_2690_ = l_Lean_MessageData_ofFormat(v___x_2689_);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2687_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
lean_inc_ref(v_e_2514_);
v___x_2694_ = l_Lean_MessageData_ofExpr(v_e_2514_);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
lean_inc(v___x_2657_);
v___x_2698_ = l_Lean_MessageData_ofExpr(v___x_2657_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__17);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
lean_inc(v___x_2590_);
v___x_2702_ = l_Lean_MessageData_ofExpr(v___x_2590_);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2677_, v___x_2703_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2706_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref(v___x_2704_);
lean_inc(v_a_2519_);
v___x_2706_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2510_, v_val_2511_, v_a_2519_, v___x_2555_, v_a_2705_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
v___y_2532_ = v___x_2706_;
goto v___jp_2531_;
}
else
{
lean_dec(v_a_2519_);
lean_dec_ref(v_e_2514_);
lean_dec(v_val_2511_);
return v___x_2704_;
}
}
}
}
v___jp_2675_:
{
lean_object* v___x_2676_; 
lean_inc(v_a_2519_);
v___x_2676_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2510_, v_val_2511_, v_a_2519_, v___x_2555_, v___x_2555_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
v___y_2532_ = v___x_2676_;
goto v___jp_2531_;
}
}
else
{
lean_del_object(v___x_2594_);
v_a_2527_ = v___x_2555_;
goto v___jp_2526_;
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_del_object(v___x_2594_);
lean_dec(v_a_2519_);
lean_dec_ref(v_e_2514_);
lean_dec(v_val_2511_);
v_a_2708_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2669_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2669_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
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
lean_object* v___x_2721_; uint8_t v___x_2722_; lean_object* v___x_2723_; 
lean_dec(v___x_2591_);
v___x_2721_ = lean_unsigned_to_nat(0u);
v___x_2722_ = 0;
lean_inc(v_a_2519_);
lean_inc(v___x_2590_);
v___x_2723_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg(v___x_2517_, v_val_2510_, v_next_2515_, v_params_2516_, v___x_2590_, v_val_2511_, v_a_2519_, v___x_2518_, v___x_2721_, v___x_2722_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; uint8_t v___x_2725_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2724_);
lean_dec_ref(v___x_2723_);
v___x_2725_ = lean_unbox(v_a_2724_);
lean_dec(v_a_2724_);
if (v___x_2725_ == 0)
{
lean_object* v_options_2726_; lean_object* v_inheritedTraceOptions_2727_; uint8_t v_hasTrace_2728_; 
v_options_2726_ = lean_ctor_get(v___y_2523_, 2);
v_inheritedTraceOptions_2727_ = lean_ctor_get(v___y_2523_, 13);
v_hasTrace_2728_ = lean_ctor_get_uint8(v_options_2726_, sizeof(void*)*1);
if (v_hasTrace_2728_ == 0)
{
goto v___jp_2729_;
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2731_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3));
v___x_2732_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6);
v___x_2733_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2727_, v_options_2726_, v___x_2732_);
if (v___x_2733_ == 0)
{
goto v___jp_2729_;
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8);
lean_inc(v_val_2511_);
v___x_2735_ = l_Nat_reprFast(v_val_2511_);
v___x_2736_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
v___x_2737_ = l_Lean_MessageData_ofFormat(v___x_2736_);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2734_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
lean_inc(v_a_2519_);
v___x_2741_ = l_Nat_reprFast(v_a_2519_);
v___x_2742_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
v___x_2743_ = l_Lean_MessageData_ofFormat(v___x_2742_);
v___x_2744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2740_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11);
v___x_2746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2744_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
lean_inc_ref(v_e_2514_);
v___x_2747_ = l_Lean_MessageData_ofExpr(v_e_2514_);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15);
v___x_2750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
lean_inc(v___x_2590_);
v___x_2751_ = l_Lean_MessageData_ofExpr(v___x_2590_);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__19);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2731_, v___x_2754_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref(v___x_2755_);
lean_inc(v_a_2519_);
v___x_2757_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2510_, v_val_2511_, v_a_2519_, v___x_2555_, v_a_2756_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
v___y_2532_ = v___x_2757_;
goto v___jp_2531_;
}
else
{
lean_dec(v_a_2519_);
lean_dec_ref(v_e_2514_);
lean_dec(v_val_2511_);
return v___x_2755_;
}
}
}
v___jp_2729_:
{
lean_object* v___x_2730_; 
lean_inc(v_a_2519_);
v___x_2730_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2510_, v_val_2511_, v_a_2519_, v___x_2555_, v___x_2555_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
v___y_2532_ = v___x_2730_;
goto v___jp_2531_;
}
}
else
{
v_a_2527_ = v___x_2555_;
goto v___jp_2526_;
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_a_2519_);
lean_dec_ref(v_e_2514_);
lean_dec(v_val_2511_);
v_a_2758_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2723_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2723_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_a_2519_);
lean_dec_ref(v_e_2514_);
lean_dec(v_val_2511_);
v_a_2766_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2588_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2588_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec(v_a_2519_);
lean_dec_ref(v_e_2514_);
lean_dec(v_val_2511_);
v_a_2774_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2553_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2553_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
v___jp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_unsigned_to_nat(1u);
v___x_2529_ = lean_nat_add(v_a_2519_, v___x_2528_);
lean_dec(v_a_2519_);
v_a_2519_ = v___x_2529_;
v_b_2520_ = v_a_2527_;
goto _start;
}
v___jp_2531_:
{
if (lean_obj_tag(v___y_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2542_; 
v_a_2533_ = lean_ctor_get(v___y_2532_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___y_2532_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2535_ = v___y_2532_;
v_isShared_2536_ = v_isSharedCheck_2542_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___y_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2542_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
if (lean_obj_tag(v_a_2533_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; 
lean_dec(v_a_2519_);
lean_dec_ref(v_e_2514_);
lean_dec(v_val_2511_);
v_a_2537_ = lean_ctor_get(v_a_2533_, 0);
lean_inc(v_a_2537_);
lean_dec_ref(v_a_2533_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v_a_2537_);
v___x_2539_ = v___x_2535_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
else
{
lean_object* v_a_2541_; 
lean_del_object(v___x_2535_);
v_a_2541_ = lean_ctor_get(v_a_2533_, 0);
lean_inc(v_a_2541_);
lean_dec_ref(v_a_2533_);
v_a_2527_ = v_a_2541_;
goto v___jp_2526_;
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec(v_a_2519_);
lean_dec_ref(v_e_2514_);
lean_dec(v_val_2511_);
v_a_2543_ = lean_ctor_get(v___y_2532_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___y_2532_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___y_2532_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___y_2532_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_val_2782_, lean_object* v_val_2783_, lean_object* v_upperBound_2784_, lean_object* v_args_2785_, lean_object* v_e_2786_, lean_object* v_next_2787_, lean_object* v_params_2788_, lean_object* v___x_2789_, lean_object* v___x_2790_, lean_object* v_a_2791_, lean_object* v_b_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
uint8_t v___x_44717__boxed_2798_; lean_object* v_res_2799_; 
v___x_44717__boxed_2798_ = lean_unbox(v___x_2790_);
v_res_2799_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2782_, v_val_2783_, v_upperBound_2784_, v_args_2785_, v_e_2786_, v_next_2787_, v_params_2788_, v___x_2789_, v___x_44717__boxed_2798_, v_a_2791_, v_b_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___x_2789_);
lean_dec_ref(v_params_2788_);
lean_dec(v_next_2787_);
lean_dec_ref(v_args_2785_);
lean_dec(v_upperBound_2784_);
lean_dec(v_val_2782_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_preDefs_2802_, lean_object* v___x_2803_, lean_object* v_val_2804_, lean_object* v_e_2805_, lean_object* v_next_2806_, lean_object* v_params_2807_, lean_object* v___x_2808_, lean_object* v_x_2809_, lean_object* v_x_2810_, lean_object* v_x_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
if (lean_obj_tag(v_x_2809_) == 5)
{
lean_object* v_fn_2817_; lean_object* v_arg_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_fn_2817_ = lean_ctor_get(v_x_2809_, 0);
lean_inc_ref(v_fn_2817_);
v_arg_2818_ = lean_ctor_get(v_x_2809_, 1);
lean_inc_ref(v_arg_2818_);
lean_dec_ref(v_x_2809_);
v___x_2819_ = lean_array_set(v_x_2810_, v_x_2811_, v_arg_2818_);
v___x_2820_ = lean_unsigned_to_nat(1u);
v___x_2821_ = lean_nat_sub(v_x_2811_, v___x_2820_);
lean_dec(v_x_2811_);
v_x_2809_ = v_fn_2817_;
v_x_2810_ = v___x_2819_;
v_x_2811_ = v___x_2821_;
goto _start;
}
else
{
uint8_t v___x_2823_; 
lean_dec(v_x_2811_);
v___x_2823_ = l_Lean_Expr_isConst(v_x_2809_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec_ref(v_x_2810_);
lean_dec_ref(v_x_2809_);
lean_dec_ref(v_e_2805_);
v___x_2824_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___closed__0));
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
return v___x_2825_;
}
else
{
lean_object* v___x_2826_; lean_object* v___f_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2826_ = l_Lean_Expr_constName_x21(v_x_2809_);
lean_dec_ref(v_x_2809_);
v___f_2827_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2827_, 0, v___x_2826_);
v___x_2828_ = lean_unsigned_to_nat(0u);
v___x_2829_ = l_Array_findIdx_x3f_loop___redArg(v___f_2827_, v_preDefs_2802_, v___x_2828_);
if (lean_obj_tag(v___x_2829_) == 1)
{
lean_object* v_val_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v_val_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_val_2830_);
lean_dec_ref(v___x_2829_);
v___x_2831_ = lean_box(0);
v___x_2832_ = lean_array_get_borrowed(v___x_2828_, v___x_2803_, v_val_2830_);
v___x_2833_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2804_, v_val_2830_, v___x_2832_, v_x_2810_, v_e_2805_, v_next_2806_, v_params_2807_, v___x_2808_, v___x_2823_, v___x_2828_, v___x_2831_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec_ref(v_x_2810_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2841_; 
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v___x_2833_, 0);
lean_dec(v_unused_2842_);
v___x_2835_ = v___x_2833_;
v_isShared_2836_ = v_isSharedCheck_2841_;
goto v_resetjp_2834_;
}
else
{
lean_dec(v___x_2833_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2841_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2837_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___closed__0));
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2837_);
v___x_2839_ = v___x_2835_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
v_a_2843_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2833_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2833_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
lean_dec(v___x_2829_);
lean_dec_ref(v_x_2810_);
lean_dec_ref(v_e_2805_);
v___x_2851_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___closed__0));
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
return v___x_2852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object* v_preDefs_2853_, lean_object* v___x_2854_, lean_object* v_val_2855_, lean_object* v_e_2856_, lean_object* v_next_2857_, lean_object* v_params_2858_, lean_object* v___x_2859_, lean_object* v_x_2860_, lean_object* v_x_2861_, lean_object* v_x_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_preDefs_2853_, v___x_2854_, v_val_2855_, v_e_2856_, v_next_2857_, v_params_2858_, v___x_2859_, v_x_2860_, v_x_2861_, v_x_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___x_2859_);
lean_dec_ref(v_params_2858_);
lean_dec(v_next_2857_);
lean_dec(v_val_2855_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v_preDefs_2853_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__1(lean_object* v_preDefs_2869_, lean_object* v___x_2870_, lean_object* v_val_2871_, lean_object* v_a_2872_, lean_object* v_params_2873_, lean_object* v___x_2874_, lean_object* v_e_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_dummy_2881_; lean_object* v_nargs_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_dummy_2881_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1);
v_nargs_2882_ = l_Lean_Expr_getAppNumArgs(v_e_2875_);
lean_inc(v_nargs_2882_);
v___x_2883_ = lean_mk_array(v_nargs_2882_, v_dummy_2881_);
v___x_2884_ = lean_unsigned_to_nat(1u);
v___x_2885_ = lean_nat_sub(v_nargs_2882_, v___x_2884_);
lean_dec(v_nargs_2882_);
lean_inc_ref(v_e_2875_);
v___x_2886_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_preDefs_2869_, v___x_2870_, v_val_2871_, v_e_2875_, v_a_2872_, v_params_2873_, v___x_2874_, v_e_2875_, v___x_2883_, v___x_2885_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__1___boxed(lean_object* v_preDefs_2887_, lean_object* v___x_2888_, lean_object* v_val_2889_, lean_object* v_a_2890_, lean_object* v_params_2891_, lean_object* v___x_2892_, lean_object* v_e_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__1(v_preDefs_2887_, v___x_2888_, v_val_2889_, v_a_2890_, v_params_2891_, v___x_2892_, v_e_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v_params_2891_);
lean_dec(v_a_2890_);
lean_dec(v_val_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v_preDefs_2887_);
return v_res_2899_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2903_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__2));
v___x_2904_ = lean_unsigned_to_nat(6u);
v___x_2905_ = lean_unsigned_to_nat(201u);
v___x_2906_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__1));
v___x_2907_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_2908_ = l_mkPanicMessageWithDecl(v___x_2907_, v___x_2906_, v___x_2905_, v___x_2904_, v___x_2903_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2(lean_object* v___x_2909_, lean_object* v___x_2910_, lean_object* v_a_2911_, lean_object* v_preDefs_2912_, lean_object* v_val_2913_, lean_object* v___f_2914_, lean_object* v___x_2915_, lean_object* v_params_2916_, lean_object* v_body_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2923_ = lean_array_get_size(v_params_2916_);
v___x_2924_ = lean_array_get_borrowed(v___x_2909_, v___x_2910_, v_a_2911_);
v___x_2925_ = lean_nat_dec_eq(v___x_2923_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_dec_ref(v_body_2917_);
lean_dec_ref(v_params_2916_);
lean_dec_ref(v___f_2914_);
lean_dec(v_val_2913_);
lean_dec_ref(v_preDefs_2912_);
lean_dec(v_a_2911_);
lean_dec_ref(v___x_2910_);
v___x_2926_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__3);
v___x_2927_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6(v___x_2926_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
return v___x_2927_;
}
else
{
lean_object* v___f_2928_; uint8_t v___x_2929_; lean_object* v___x_2930_; 
v___f_2928_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_2928_, 0, v_preDefs_2912_);
lean_closure_set(v___f_2928_, 1, v___x_2910_);
lean_closure_set(v___f_2928_, 2, v_val_2913_);
lean_closure_set(v___f_2928_, 3, v_a_2911_);
lean_closure_set(v___f_2928_, 4, v_params_2916_);
lean_closure_set(v___f_2928_, 5, v___x_2923_);
v___x_2929_ = 0;
v___x_2930_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7(v_body_2917_, v___f_2928_, v___f_2914_, v___x_2929_, v___x_2925_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2937_ == 0)
{
lean_object* v_unused_2938_; 
v_unused_2938_ = lean_ctor_get(v___x_2930_, 0);
lean_dec(v_unused_2938_);
v___x_2932_ = v___x_2930_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_dec(v___x_2930_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2915_);
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2915_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
v_a_2939_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2930_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2930_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___boxed(lean_object* v___x_2947_, lean_object* v___x_2948_, lean_object* v_a_2949_, lean_object* v_preDefs_2950_, lean_object* v_val_2951_, lean_object* v___f_2952_, lean_object* v___x_2953_, lean_object* v_params_2954_, lean_object* v_body_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2(v___x_2947_, v___x_2948_, v_a_2949_, v_preDefs_2950_, v_val_2951_, v___f_2952_, v___x_2953_, v_params_2954_, v_body_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___x_2947_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg(lean_object* v_preDefs_2963_, lean_object* v___x_2964_, lean_object* v_val_2965_, lean_object* v_upperBound_2966_, lean_object* v_a_2967_, lean_object* v_b_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
uint8_t v___x_2974_; 
v___x_2974_ = lean_nat_dec_lt(v_a_2967_, v_upperBound_2966_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; 
lean_dec(v_a_2967_);
lean_dec(v_val_2965_);
lean_dec_ref(v___x_2964_);
lean_dec_ref(v_preDefs_2963_);
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v_b_2968_);
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; lean_object* v_value_2977_; lean_object* v___f_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___f_2981_; uint8_t v___x_2982_; lean_object* v___x_2983_; 
v___x_2976_ = lean_array_fget_borrowed(v_preDefs_2963_, v_a_2967_);
v_value_2977_ = lean_ctor_get(v___x_2976_, 7);
v___f_2978_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___closed__0));
v___x_2979_ = lean_unsigned_to_nat(0u);
v___x_2980_ = lean_box(0);
lean_inc(v_val_2965_);
lean_inc_ref(v_preDefs_2963_);
lean_inc(v_a_2967_);
lean_inc_ref(v___x_2964_);
v___f_2981_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_2981_, 0, v___x_2979_);
lean_closure_set(v___f_2981_, 1, v___x_2964_);
lean_closure_set(v___f_2981_, 2, v_a_2967_);
lean_closure_set(v___f_2981_, 3, v_preDefs_2963_);
lean_closure_set(v___f_2981_, 4, v_val_2965_);
lean_closure_set(v___f_2981_, 5, v___f_2978_);
lean_closure_set(v___f_2981_, 6, v___x_2980_);
v___x_2982_ = 0;
lean_inc_ref(v_value_2977_);
v___x_2983_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_2977_, v___f_2981_, v___x_2982_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
lean_dec_ref(v___x_2983_);
v___x_2984_ = lean_unsigned_to_nat(1u);
v___x_2985_ = lean_nat_add(v_a_2967_, v___x_2984_);
lean_dec(v_a_2967_);
v_a_2967_ = v___x_2985_;
v_b_2968_ = v___x_2980_;
goto _start;
}
else
{
lean_dec(v_a_2967_);
lean_dec(v_val_2965_);
lean_dec_ref(v___x_2964_);
lean_dec_ref(v_preDefs_2963_);
return v___x_2983_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___boxed(lean_object* v_preDefs_2987_, lean_object* v___x_2988_, lean_object* v_val_2989_, lean_object* v_upperBound_2990_, lean_object* v_a_2991_, lean_object* v_b_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg(v_preDefs_2987_, v___x_2988_, v_val_2989_, v_upperBound_2990_, v_a_2991_, v_b_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v_upperBound_2990_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(size_t v_sz_2999_, size_t v_i_3000_, lean_object* v_bs_3001_){
_start:
{
uint8_t v___x_3002_; 
v___x_3002_ = lean_usize_dec_lt(v_i_3000_, v_sz_2999_);
if (v___x_3002_ == 0)
{
return v_bs_3001_;
}
else
{
lean_object* v_v_3003_; lean_object* v___x_3004_; lean_object* v_bs_x27_3005_; lean_object* v___x_3006_; size_t v___x_3007_; size_t v___x_3008_; lean_object* v___x_3009_; 
v_v_3003_ = lean_array_uget(v_bs_3001_, v_i_3000_);
v___x_3004_ = lean_unsigned_to_nat(0u);
v_bs_x27_3005_ = lean_array_uset(v_bs_3001_, v_i_3000_, v___x_3004_);
v___x_3006_ = lean_array_get_size(v_v_3003_);
lean_dec(v_v_3003_);
v___x_3007_ = ((size_t)1ULL);
v___x_3008_ = lean_usize_add(v_i_3000_, v___x_3007_);
v___x_3009_ = lean_array_uset(v_bs_x27_3005_, v_i_3000_, v___x_3006_);
v_i_3000_ = v___x_3008_;
v_bs_3001_ = v___x_3009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1___boxed(lean_object* v_sz_3011_, lean_object* v_i_3012_, lean_object* v_bs_3013_){
_start:
{
size_t v_sz_boxed_3014_; size_t v_i_boxed_3015_; lean_object* v_res_3016_; 
v_sz_boxed_3014_ = lean_unbox_usize(v_sz_3011_);
lean_dec(v_sz_3011_);
v_i_boxed_3015_ = lean_unbox_usize(v_i_3012_);
lean_dec(v_i_3012_);
v_res_3016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_boxed_3014_, v_i_boxed_3015_, v_bs_3013_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(size_t v_sz_3017_, size_t v_i_3018_, lean_object* v_bs_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
uint8_t v___x_3025_; 
v___x_3025_ = lean_usize_dec_lt(v_i_3018_, v_sz_3017_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3026_, 0, v_bs_3019_);
return v___x_3026_;
}
else
{
lean_object* v_v_3027_; lean_object* v_value_3028_; lean_object* v___x_3029_; 
v_v_3027_ = lean_array_uget_borrowed(v_bs_3019_, v_i_3018_);
v_value_3028_ = lean_ctor_get(v_v_3027_, 7);
lean_inc_ref(v_value_3028_);
v___x_3029_ = l_Lean_Elab_getParamRevDeps(v_value_3028_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3031_; lean_object* v_bs_x27_3032_; size_t v___x_3033_; size_t v___x_3034_; lean_object* v___x_3035_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref(v___x_3029_);
v___x_3031_ = lean_unsigned_to_nat(0u);
v_bs_x27_3032_ = lean_array_uset(v_bs_3019_, v_i_3018_, v___x_3031_);
v___x_3033_ = ((size_t)1ULL);
v___x_3034_ = lean_usize_add(v_i_3018_, v___x_3033_);
v___x_3035_ = lean_array_uset(v_bs_x27_3032_, v_i_3018_, v_a_3030_);
v_i_3018_ = v___x_3034_;
v_bs_3019_ = v___x_3035_;
goto _start;
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref(v_bs_3019_);
v_a_3037_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3029_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3029_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0___boxed(lean_object* v_sz_3045_, lean_object* v_i_3046_, lean_object* v_bs_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
size_t v_sz_boxed_3053_; size_t v_i_boxed_3054_; lean_object* v_res_3055_; 
v_sz_boxed_3053_ = lean_unbox_usize(v_sz_3045_);
lean_dec(v_sz_3045_);
v_i_boxed_3054_ = lean_unbox_usize(v_i_3046_);
lean_dec(v_i_3046_);
v_res_3055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_boxed_3053_, v_i_boxed_3054_, v_bs_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
return v_res_3055_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3058_ = l_Lean_stringToMessageData(v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
size_t v_sz_3065_; size_t v___x_3066_; lean_object* v___x_3067_; 
v_sz_3065_ = lean_array_size(v_preDefs_3059_);
v___x_3066_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3059_);
v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3065_, v___x_3066_, v_preDefs_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; size_t v_sz_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc_n(v_a_3068_, 2);
lean_dec_ref(v___x_3067_);
v_sz_3069_ = lean_array_size(v_a_3068_);
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3069_, v___x_3066_, v_a_3068_);
v___x_3071_ = l_Lean_Elab_FixedParams_Info_init(v_a_3068_);
v___x_3072_ = lean_st_mk_ref(v___x_3071_);
v___x_3073_ = lean_st_ref_take(v___x_3072_);
v___x_3074_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3073_);
v___x_3075_ = lean_st_ref_set(v___x_3072_, v___x_3074_);
v___x_3076_ = lean_array_get_size(v_preDefs_3059_);
v___x_3077_ = lean_unsigned_to_nat(0u);
v___x_3078_ = lean_box(0);
lean_inc(v___x_3072_);
v___x_3079_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg(v_preDefs_3059_, v___x_3070_, v___x_3072_, v___x_3076_, v___x_3077_, v___x_3078_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3118_; 
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3118_ == 0)
{
lean_object* v_unused_3119_; 
v_unused_3119_ = lean_ctor_get(v___x_3079_, 0);
lean_dec(v_unused_3119_);
v___x_3081_ = v___x_3079_;
v_isShared_3082_ = v_isSharedCheck_3118_;
goto v_resetjp_3080_;
}
else
{
lean_dec(v___x_3079_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3118_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v_options_3084_; uint8_t v_hasTrace_3085_; 
v___x_3083_ = lean_st_ref_get(v___x_3072_);
lean_dec(v___x_3072_);
v_options_3084_ = lean_ctor_get(v_a_3062_, 2);
v_hasTrace_3085_ = lean_ctor_get_uint8(v_options_3084_, sizeof(void*)*1);
if (v_hasTrace_3085_ == 0)
{
lean_object* v___x_3087_; 
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 0, v___x_3083_);
v___x_3087_ = v___x_3081_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3083_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v_inheritedTraceOptions_3089_ = lean_ctor_get(v_a_3062_, 13);
v___x_3090_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3));
v___x_3091_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6);
v___x_3092_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3089_, v_options_3084_, v___x_3091_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3094_; 
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 0, v___x_3083_);
v___x_3094_ = v___x_3081_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3083_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
lean_del_object(v___x_3081_);
v___x_3096_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3083_);
v___x_3097_ = l_Lean_Elab_FixedParams_Info_format(v___x_3083_);
v___x_3098_ = l_Std_Format_indentD(v___x_3097_);
v___x_3099_ = l_Lean_MessageData_ofFormat(v___x_3098_);
v___x_3100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3096_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3090_, v___x_3100_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3108_ == 0)
{
lean_object* v_unused_3109_; 
v_unused_3109_ = lean_ctor_get(v___x_3101_, 0);
lean_dec(v_unused_3109_);
v___x_3103_ = v___x_3101_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_dec(v___x_3101_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3083_);
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3083_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v___x_3083_);
v_a_3110_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3101_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3101_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v___x_3072_);
v_a_3120_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3079_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3079_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec_ref(v_preDefs_3059_);
v_a_3128_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3067_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3067_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_);
lean_dec(v_a_3140_);
lean_dec_ref(v_a_3139_);
lean_dec(v_a_3138_);
lean_dec_ref(v_a_3137_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v_upperBound_3143_, lean_object* v_val_3144_, lean_object* v_next_3145_, lean_object* v_params_3146_, lean_object* v___x_3147_, lean_object* v_val_3148_, lean_object* v_next_3149_, uint8_t v___x_3150_, lean_object* v_inst_3151_, lean_object* v_R_3152_, lean_object* v_a_3153_, uint8_t v_b_3154_, lean_object* v_c_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg(v_upperBound_3143_, v_val_3144_, v_next_3145_, v_params_3146_, v___x_3147_, v_val_3148_, v_next_3149_, v___x_3150_, v_a_3153_, v_b_3154_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3162_ = _args[0];
lean_object* v_val_3163_ = _args[1];
lean_object* v_next_3164_ = _args[2];
lean_object* v_params_3165_ = _args[3];
lean_object* v___x_3166_ = _args[4];
lean_object* v_val_3167_ = _args[5];
lean_object* v_next_3168_ = _args[6];
lean_object* v___x_3169_ = _args[7];
lean_object* v_inst_3170_ = _args[8];
lean_object* v_R_3171_ = _args[9];
lean_object* v_a_3172_ = _args[10];
lean_object* v_b_3173_ = _args[11];
lean_object* v_c_3174_ = _args[12];
lean_object* v___y_3175_ = _args[13];
lean_object* v___y_3176_ = _args[14];
lean_object* v___y_3177_ = _args[15];
lean_object* v___y_3178_ = _args[16];
lean_object* v___y_3179_ = _args[17];
_start:
{
uint8_t v___x_45712__boxed_3180_; uint8_t v_b_boxed_3181_; lean_object* v_res_3182_; 
v___x_45712__boxed_3180_ = lean_unbox(v___x_3169_);
v_b_boxed_3181_ = lean_unbox(v_b_3173_);
v_res_3182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3(v_upperBound_3162_, v_val_3163_, v_next_3164_, v_params_3165_, v___x_3166_, v_val_3167_, v_next_3168_, v___x_45712__boxed_3180_, v_inst_3170_, v_R_3171_, v_a_3172_, v_b_boxed_3181_, v_c_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v_val_3167_);
lean_dec_ref(v_params_3165_);
lean_dec(v_next_3164_);
lean_dec(v_val_3163_);
lean_dec(v_upperBound_3162_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_val_3183_, lean_object* v_val_3184_, lean_object* v_upperBound_3185_, lean_object* v_args_3186_, lean_object* v_e_3187_, lean_object* v_next_3188_, lean_object* v_params_3189_, lean_object* v___x_3190_, uint8_t v___x_3191_, lean_object* v_inst_3192_, lean_object* v_R_3193_, lean_object* v_a_3194_, lean_object* v_b_3195_, lean_object* v_c_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_3183_, v_val_3184_, v_upperBound_3185_, v_args_3186_, v_e_3187_, v_next_3188_, v_params_3189_, v___x_3190_, v___x_3191_, v_a_3194_, v_b_3195_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_val_3203_ = _args[0];
lean_object* v_val_3204_ = _args[1];
lean_object* v_upperBound_3205_ = _args[2];
lean_object* v_args_3206_ = _args[3];
lean_object* v_e_3207_ = _args[4];
lean_object* v_next_3208_ = _args[5];
lean_object* v_params_3209_ = _args[6];
lean_object* v___x_3210_ = _args[7];
lean_object* v___x_3211_ = _args[8];
lean_object* v_inst_3212_ = _args[9];
lean_object* v_R_3213_ = _args[10];
lean_object* v_a_3214_ = _args[11];
lean_object* v_b_3215_ = _args[12];
lean_object* v_c_3216_ = _args[13];
lean_object* v___y_3217_ = _args[14];
lean_object* v___y_3218_ = _args[15];
lean_object* v___y_3219_ = _args[16];
lean_object* v___y_3220_ = _args[17];
lean_object* v___y_3221_ = _args[18];
_start:
{
uint8_t v___x_45747__boxed_3222_; lean_object* v_res_3223_; 
v___x_45747__boxed_3222_ = lean_unbox(v___x_3211_);
v_res_3223_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_val_3203_, v_val_3204_, v_upperBound_3205_, v_args_3206_, v_e_3207_, v_next_3208_, v_params_3209_, v___x_3210_, v___x_45747__boxed_3222_, v_inst_3212_, v_R_3213_, v_a_3214_, v_b_3215_, v_c_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___x_3210_);
lean_dec_ref(v_params_3209_);
lean_dec(v_next_3208_);
lean_dec_ref(v_args_3206_);
lean_dec(v_upperBound_3205_);
lean_dec(v_val_3203_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_preDefs_3224_, lean_object* v___x_3225_, lean_object* v_val_3226_, lean_object* v_upperBound_3227_, lean_object* v_inst_3228_, lean_object* v_R_3229_, lean_object* v_a_3230_, lean_object* v_b_3231_, lean_object* v_c_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg(v_preDefs_3224_, v___x_3225_, v_val_3226_, v_upperBound_3227_, v_a_3230_, v_b_3231_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_preDefs_3239_, lean_object* v___x_3240_, lean_object* v_val_3241_, lean_object* v_upperBound_3242_, lean_object* v_inst_3243_, lean_object* v_R_3244_, lean_object* v_a_3245_, lean_object* v_b_3246_, lean_object* v_c_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_preDefs_3239_, v___x_3240_, v_val_3241_, v_upperBound_3242_, v_inst_3243_, v_R_3244_, v_a_3245_, v_b_3246_, v_c_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v_upperBound_3242_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11(lean_object* v_upperBound_3254_, lean_object* v___x_3255_, lean_object* v_pre_3256_, lean_object* v_post_3257_, uint8_t v_usedLetOnly_3258_, uint8_t v_skipConstInApp_3259_, uint8_t v_skipInstances_3260_, lean_object* v___x_3261_, lean_object* v_inst_3262_, lean_object* v_R_3263_, lean_object* v_a_3264_, lean_object* v_b_3265_, lean_object* v_c_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg(v_upperBound_3254_, v___x_3255_, v_pre_3256_, v_post_3257_, v_usedLetOnly_3258_, v_skipConstInApp_3259_, v_skipInstances_3260_, v_a_3264_, v_b_3265_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___boxed(lean_object** _args){
lean_object* v_upperBound_3274_ = _args[0];
lean_object* v___x_3275_ = _args[1];
lean_object* v_pre_3276_ = _args[2];
lean_object* v_post_3277_ = _args[3];
lean_object* v_usedLetOnly_3278_ = _args[4];
lean_object* v_skipConstInApp_3279_ = _args[5];
lean_object* v_skipInstances_3280_ = _args[6];
lean_object* v___x_3281_ = _args[7];
lean_object* v_inst_3282_ = _args[8];
lean_object* v_R_3283_ = _args[9];
lean_object* v_a_3284_ = _args[10];
lean_object* v_b_3285_ = _args[11];
lean_object* v_c_3286_ = _args[12];
lean_object* v___y_3287_ = _args[13];
lean_object* v___y_3288_ = _args[14];
lean_object* v___y_3289_ = _args[15];
lean_object* v___y_3290_ = _args[16];
lean_object* v___y_3291_ = _args[17];
lean_object* v___y_3292_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3293_; uint8_t v_skipConstInApp_boxed_3294_; uint8_t v_skipInstances_boxed_3295_; lean_object* v_res_3296_; 
v_usedLetOnly_boxed_3293_ = lean_unbox(v_usedLetOnly_3278_);
v_skipConstInApp_boxed_3294_ = lean_unbox(v_skipConstInApp_3279_);
v_skipInstances_boxed_3295_ = lean_unbox(v_skipInstances_3280_);
v_res_3296_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11(v_upperBound_3274_, v___x_3275_, v_pre_3276_, v_post_3277_, v_usedLetOnly_boxed_3293_, v_skipConstInApp_boxed_3294_, v_skipInstances_boxed_3295_, v___x_3281_, v_inst_3282_, v_R_3283_, v_a_3284_, v_b_3285_, v_c_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec(v___x_3281_);
lean_dec_ref(v___x_3275_);
lean_dec(v_upperBound_3274_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12(lean_object* v_00_u03b2_3297_, lean_object* v_m_3298_, lean_object* v_a_3299_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12___redArg(v_m_3298_, v_a_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3301_, lean_object* v_m_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12(v_00_u03b2_3301_, v_m_3302_, v_a_3303_);
lean_dec_ref(v_a_3303_);
lean_dec_ref(v_m_3302_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16(lean_object* v_00_u03b1_3305_, lean_object* v_name_3306_, uint8_t v_bi_3307_, lean_object* v_type_3308_, lean_object* v_k_3309_, uint8_t v_kind_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg(v_name_3306_, v_bi_3307_, v_type_3308_, v_k_3309_, v_kind_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___boxed(lean_object* v_00_u03b1_3318_, lean_object* v_name_3319_, lean_object* v_bi_3320_, lean_object* v_type_3321_, lean_object* v_k_3322_, lean_object* v_kind_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v_bi_boxed_3330_; uint8_t v_kind_boxed_3331_; lean_object* v_res_3332_; 
v_bi_boxed_3330_ = lean_unbox(v_bi_3320_);
v_kind_boxed_3331_ = lean_unbox(v_kind_3323_);
v_res_3332_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16(v_00_u03b1_3318_, v_name_3319_, v_bi_boxed_3330_, v_type_3321_, v_k_3322_, v_kind_boxed_3331_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19(lean_object* v_00_u03b1_3333_, lean_object* v_name_3334_, lean_object* v_type_3335_, lean_object* v_val_3336_, lean_object* v_k_3337_, uint8_t v_nondep_3338_, uint8_t v_kind_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v___x_3346_; 
v___x_3346_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19___redArg(v_name_3334_, v_type_3335_, v_val_3336_, v_k_3337_, v_nondep_3338_, v_kind_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19___boxed(lean_object* v_00_u03b1_3347_, lean_object* v_name_3348_, lean_object* v_type_3349_, lean_object* v_val_3350_, lean_object* v_k_3351_, lean_object* v_nondep_3352_, lean_object* v_kind_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
uint8_t v_nondep_boxed_3360_; uint8_t v_kind_boxed_3361_; lean_object* v_res_3362_; 
v_nondep_boxed_3360_ = lean_unbox(v_nondep_3352_);
v_kind_boxed_3361_ = lean_unbox(v_kind_3353_);
v_res_3362_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19(v_00_u03b1_3347_, v_name_3348_, v_type_3349_, v_val_3350_, v_k_3351_, v_nondep_boxed_3360_, v_kind_boxed_3361_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22(lean_object* v_00_u03b1_3363_, lean_object* v_ref_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg(v_ref_3364_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___boxed(lean_object* v_00_u03b1_3371_, lean_object* v_ref_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22(v_00_u03b1_3371_, v_ref_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17(lean_object* v_00_u03b1_3379_, lean_object* v_x_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v___x_3387_; 
v___x_3387_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___redArg(v_x_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___boxed(lean_object* v_00_u03b1_3388_, lean_object* v_x_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17(v_00_u03b1_3388_, v_x_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18(lean_object* v_00_u03b2_3397_, lean_object* v_m_3398_, lean_object* v_a_3399_, lean_object* v_b_3400_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18___redArg(v_m_3398_, v_a_3399_, v_b_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14(lean_object* v_00_u03b2_3402_, lean_object* v_a_3403_, lean_object* v_x_3404_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14___redArg(v_a_3403_, v_x_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14___boxed(lean_object* v_00_u03b2_3406_, lean_object* v_a_3407_, lean_object* v_x_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14(v_00_u03b2_3406_, v_a_3407_, v_x_3408_);
lean_dec(v_x_3408_);
lean_dec_ref(v_a_3407_);
return v_res_3409_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24(lean_object* v_00_u03b2_3410_, lean_object* v_a_3411_, lean_object* v_x_3412_){
_start:
{
uint8_t v___x_3413_; 
v___x_3413_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24___redArg(v_a_3411_, v_x_3412_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24___boxed(lean_object* v_00_u03b2_3414_, lean_object* v_a_3415_, lean_object* v_x_3416_){
_start:
{
uint8_t v_res_3417_; lean_object* v_r_3418_; 
v_res_3417_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24(v_00_u03b2_3414_, v_a_3415_, v_x_3416_);
lean_dec(v_x_3416_);
lean_dec_ref(v_a_3415_);
v_r_3418_ = lean_box(v_res_3417_);
return v_r_3418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25(lean_object* v_00_u03b2_3419_, lean_object* v_data_3420_){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25___redArg(v_data_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__26(lean_object* v_00_u03b2_3422_, lean_object* v_a_3423_, lean_object* v_b_3424_, lean_object* v_x_3425_){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__26___redArg(v_a_3423_, v_b_3424_, v_x_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26(lean_object* v_00_u03b2_3427_, lean_object* v_i_3428_, lean_object* v_source_3429_, lean_object* v_target_3430_){
_start:
{
lean_object* v___x_3431_; 
v___x_3431_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26___redArg(v_i_3428_, v_source_3429_, v_target_3430_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26_spec__27(lean_object* v_00_u03b2_3432_, lean_object* v_x_3433_, lean_object* v_x_3434_){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26_spec__27___redArg(v_x_3433_, v_x_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3449_, lean_object* v_x_3450_){
_start:
{
if (lean_obj_tag(v_x_3449_) == 0)
{
lean_object* v___x_3451_; 
v___x_3451_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3451_;
}
else
{
lean_object* v_val_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3463_; 
v_val_3452_ = lean_ctor_get(v_x_3449_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_x_3449_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3454_ = v_x_3449_;
v_isShared_3455_ = v_isSharedCheck_3463_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_val_3452_);
lean_dec(v_x_3449_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3463_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3456_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3457_ = l_Nat_reprFast(v_val_3452_);
if (v_isShared_3455_ == 0)
{
lean_ctor_set_tag(v___x_3454_, 3);
lean_ctor_set(v___x_3454_, 0, v___x_3457_);
v___x_3459_ = v___x_3454_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3456_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = l_Repr_addAppParen(v___x_3460_, v_x_3450_);
return v___x_3461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3464_, lean_object* v_x_3465_){
_start:
{
lean_object* v_res_3466_; 
v_res_3466_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3464_, v_x_3465_);
lean_dec(v_x_3465_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3467_, lean_object* v_x_3468_, lean_object* v_x_3469_){
_start:
{
if (lean_obj_tag(v_x_3469_) == 0)
{
lean_dec(v_x_3467_);
return v_x_3468_;
}
else
{
lean_object* v_head_3470_; lean_object* v_tail_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3482_; 
v_head_3470_ = lean_ctor_get(v_x_3469_, 0);
v_tail_3471_ = lean_ctor_get(v_x_3469_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_x_3469_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3473_ = v_x_3469_;
v_isShared_3474_ = v_isSharedCheck_3482_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_tail_3471_);
lean_inc(v_head_3470_);
lean_dec(v_x_3469_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3482_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
lean_inc(v_x_3467_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set_tag(v___x_3473_, 5);
lean_ctor_set(v___x_3473_, 1, v_x_3467_);
lean_ctor_set(v___x_3473_, 0, v_x_3468_);
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_x_3468_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_x_3467_);
v___x_3476_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3477_ = lean_unsigned_to_nat(0u);
v___x_3478_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3470_, v___x_3477_);
v___x_3479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3476_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
v_x_3468_ = v___x_3479_;
v_x_3469_ = v_tail_3471_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3483_, lean_object* v_x_3484_, lean_object* v_x_3485_){
_start:
{
if (lean_obj_tag(v_x_3485_) == 0)
{
lean_dec(v_x_3483_);
return v_x_3484_;
}
else
{
lean_object* v_head_3486_; lean_object* v_tail_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3498_; 
v_head_3486_ = lean_ctor_get(v_x_3485_, 0);
v_tail_3487_ = lean_ctor_get(v_x_3485_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_x_3485_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3489_ = v_x_3485_;
v_isShared_3490_ = v_isSharedCheck_3498_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_tail_3487_);
lean_inc(v_head_3486_);
lean_dec(v_x_3485_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3498_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
lean_inc(v_x_3483_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set_tag(v___x_3489_, 5);
lean_ctor_set(v___x_3489_, 1, v_x_3483_);
lean_ctor_set(v___x_3489_, 0, v_x_3484_);
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_x_3484_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_x_3483_);
v___x_3492_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3493_ = lean_unsigned_to_nat(0u);
v___x_3494_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3486_, v___x_3493_);
v___x_3495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3492_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3483_, v___x_3495_, v_tail_3487_);
return v___x_3496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = lean_unsigned_to_nat(0u);
v___x_3501_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3499_, v___x_3500_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3502_, lean_object* v_x_3503_){
_start:
{
if (lean_obj_tag(v_x_3502_) == 0)
{
lean_object* v___x_3504_; 
lean_dec(v_x_3503_);
v___x_3504_ = lean_box(0);
return v___x_3504_;
}
else
{
lean_object* v_tail_3505_; 
v_tail_3505_ = lean_ctor_get(v_x_3502_, 1);
if (lean_obj_tag(v_tail_3505_) == 0)
{
lean_object* v_head_3506_; lean_object* v___x_3507_; 
lean_dec(v_x_3503_);
v_head_3506_ = lean_ctor_get(v_x_3502_, 0);
lean_inc(v_head_3506_);
lean_dec_ref(v_x_3502_);
v___x_3507_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3506_);
return v___x_3507_;
}
else
{
lean_object* v_head_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
lean_inc(v_tail_3505_);
v_head_3508_ = lean_ctor_get(v_x_3502_, 0);
lean_inc(v_head_3508_);
lean_dec_ref(v_x_3502_);
v___x_3509_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3508_);
v___x_3510_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3503_, v___x_3509_, v_tail_3505_);
return v___x_3510_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3519_ = lean_string_length(v___x_3518_);
return v___x_3519_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3521_ = lean_nat_to_int(v___x_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3527_){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v___x_3528_ = lean_array_get_size(v_xs_3527_);
v___x_3529_ = lean_unsigned_to_nat(0u);
v___x_3530_ = lean_nat_dec_eq(v___x_3528_, v___x_3529_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3531_ = lean_array_to_list(v_xs_3527_);
v___x_3532_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3533_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3531_, v___x_3532_);
v___x_3534_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3535_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
lean_ctor_set(v___x_3536_, 1, v___x_3533_);
v___x_3537_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3536_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3534_);
lean_ctor_set(v___x_3539_, 1, v___x_3538_);
v___x_3540_ = l_Std_Format_fill(v___x_3539_);
return v___x_3540_;
}
else
{
lean_object* v___x_3541_; 
lean_dec_ref(v_xs_3527_);
v___x_3541_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3541_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3542_, lean_object* v_x_3543_, lean_object* v_x_3544_){
_start:
{
if (lean_obj_tag(v_x_3544_) == 0)
{
lean_dec(v_x_3542_);
return v_x_3543_;
}
else
{
lean_object* v_head_3545_; lean_object* v_tail_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3556_; 
v_head_3545_ = lean_ctor_get(v_x_3544_, 0);
v_tail_3546_ = lean_ctor_get(v_x_3544_, 1);
v_isSharedCheck_3556_ = !lean_is_exclusive(v_x_3544_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3548_ = v_x_3544_;
v_isShared_3549_ = v_isSharedCheck_3556_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_tail_3546_);
lean_inc(v_head_3545_);
lean_dec(v_x_3544_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3556_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
lean_inc(v_x_3542_);
if (v_isShared_3549_ == 0)
{
lean_ctor_set_tag(v___x_3548_, 5);
lean_ctor_set(v___x_3548_, 1, v_x_3542_);
lean_ctor_set(v___x_3548_, 0, v_x_3543_);
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_x_3543_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_x_3542_);
v___x_3551_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3545_);
v___x_3553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3551_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
v_x_3543_ = v___x_3553_;
v_x_3544_ = v_tail_3546_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3557_, lean_object* v_x_3558_){
_start:
{
if (lean_obj_tag(v_x_3557_) == 0)
{
lean_object* v___x_3559_; 
lean_dec(v_x_3558_);
v___x_3559_ = lean_box(0);
return v___x_3559_;
}
else
{
lean_object* v_tail_3560_; 
v_tail_3560_ = lean_ctor_get(v_x_3557_, 1);
if (lean_obj_tag(v_tail_3560_) == 0)
{
lean_object* v_head_3561_; lean_object* v___x_3562_; 
lean_dec(v_x_3558_);
v_head_3561_ = lean_ctor_get(v_x_3557_, 0);
lean_inc(v_head_3561_);
lean_dec_ref(v_x_3557_);
v___x_3562_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3561_);
return v___x_3562_;
}
else
{
lean_object* v_head_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_inc(v_tail_3560_);
v_head_3563_ = lean_ctor_get(v_x_3557_, 0);
lean_inc(v_head_3563_);
lean_dec_ref(v_x_3557_);
v___x_3564_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3563_);
v___x_3565_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3558_, v___x_3564_, v_tail_3560_);
return v___x_3565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3566_){
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
v___x_3572_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3570_, v___x_3571_);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3581_, lean_object* v_x_3582_, lean_object* v_x_3583_){
_start:
{
if (lean_obj_tag(v_x_3583_) == 0)
{
lean_dec(v_x_3581_);
return v_x_3582_;
}
else
{
lean_object* v_head_3584_; lean_object* v_tail_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3596_; 
v_head_3584_ = lean_ctor_get(v_x_3583_, 0);
v_tail_3585_ = lean_ctor_get(v_x_3583_, 1);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_x_3583_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3587_ = v_x_3583_;
v_isShared_3588_ = v_isSharedCheck_3596_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_tail_3585_);
lean_inc(v_head_3584_);
lean_dec(v_x_3583_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3596_;
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
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_x_3582_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_x_3581_);
v___x_3590_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = l_Nat_reprFast(v_head_3584_);
v___x_3592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
v___x_3593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3590_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v_x_3582_ = v___x_3593_;
v_x_3583_ = v_tail_3585_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3597_, lean_object* v_x_3598_, lean_object* v_x_3599_){
_start:
{
if (lean_obj_tag(v_x_3599_) == 0)
{
lean_dec(v_x_3597_);
return v_x_3598_;
}
else
{
lean_object* v_head_3600_; lean_object* v_tail_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3612_; 
v_head_3600_ = lean_ctor_get(v_x_3599_, 0);
v_tail_3601_ = lean_ctor_get(v_x_3599_, 1);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_x_3599_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3603_ = v_x_3599_;
v_isShared_3604_ = v_isSharedCheck_3612_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_tail_3601_);
lean_inc(v_head_3600_);
lean_dec(v_x_3599_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3612_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
lean_inc(v_x_3597_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set_tag(v___x_3603_, 5);
lean_ctor_set(v___x_3603_, 1, v_x_3597_);
lean_ctor_set(v___x_3603_, 0, v_x_3598_);
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_x_3598_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_x_3597_);
v___x_3606_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3607_ = l_Nat_reprFast(v_head_3600_);
v___x_3608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
v___x_3609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3606_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3597_, v___x_3609_, v_tail_3601_);
return v___x_3610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3613_){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = l_Nat_reprFast(v___y_3613_);
v___x_3615_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3616_, lean_object* v_x_3617_){
_start:
{
if (lean_obj_tag(v_x_3616_) == 0)
{
lean_object* v___x_3618_; 
lean_dec(v_x_3617_);
v___x_3618_ = lean_box(0);
return v___x_3618_;
}
else
{
lean_object* v_tail_3619_; 
v_tail_3619_ = lean_ctor_get(v_x_3616_, 1);
if (lean_obj_tag(v_tail_3619_) == 0)
{
lean_object* v_head_3620_; lean_object* v___x_3621_; 
lean_dec(v_x_3617_);
v_head_3620_ = lean_ctor_get(v_x_3616_, 0);
lean_inc(v_head_3620_);
lean_dec_ref(v_x_3616_);
v___x_3621_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3620_);
return v___x_3621_;
}
else
{
lean_object* v_head_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
lean_inc(v_tail_3619_);
v_head_3622_ = lean_ctor_get(v_x_3616_, 0);
lean_inc(v_head_3622_);
lean_dec_ref(v_x_3616_);
v___x_3623_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3622_);
v___x_3624_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3617_, v___x_3623_, v_tail_3619_);
return v___x_3624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3625_){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3626_ = lean_array_get_size(v_xs_3625_);
v___x_3627_ = lean_unsigned_to_nat(0u);
v___x_3628_ = lean_nat_dec_eq(v___x_3626_, v___x_3627_);
if (v___x_3628_ == 0)
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3629_ = lean_array_to_list(v_xs_3625_);
v___x_3630_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3631_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3629_, v___x_3630_);
v___x_3632_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3633_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
lean_ctor_set(v___x_3634_, 1, v___x_3631_);
v___x_3635_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3634_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
v___x_3637_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3632_);
lean_ctor_set(v___x_3637_, 1, v___x_3636_);
v___x_3638_ = l_Std_Format_fill(v___x_3637_);
return v___x_3638_;
}
else
{
lean_object* v___x_3639_; 
lean_dec_ref(v_xs_3625_);
v___x_3639_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3639_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3640_, lean_object* v_x_3641_, lean_object* v_x_3642_){
_start:
{
if (lean_obj_tag(v_x_3642_) == 0)
{
lean_dec(v_x_3640_);
return v_x_3641_;
}
else
{
lean_object* v_head_3643_; lean_object* v_tail_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3654_; 
v_head_3643_ = lean_ctor_get(v_x_3642_, 0);
v_tail_3644_ = lean_ctor_get(v_x_3642_, 1);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_x_3642_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3646_ = v_x_3642_;
v_isShared_3647_ = v_isSharedCheck_3654_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_tail_3644_);
lean_inc(v_head_3643_);
lean_dec(v_x_3642_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3654_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
lean_inc(v_x_3640_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set_tag(v___x_3646_, 5);
lean_ctor_set(v___x_3646_, 1, v_x_3640_);
lean_ctor_set(v___x_3646_, 0, v_x_3641_);
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_x_3641_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_x_3640_);
v___x_3649_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3643_);
v___x_3651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3649_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v_x_3641_ = v___x_3651_;
v_x_3642_ = v_tail_3644_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3655_, lean_object* v_x_3656_){
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
lean_dec_ref(v_x_3655_);
v___x_3660_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3659_);
return v___x_3660_;
}
else
{
lean_object* v_head_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
lean_inc(v_tail_3658_);
v_head_3661_ = lean_ctor_get(v_x_3655_, 0);
lean_inc(v_head_3661_);
lean_dec_ref(v_x_3655_);
v___x_3662_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3661_);
v___x_3663_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3656_, v___x_3662_, v_tail_3658_);
return v___x_3663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3664_){
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
v___x_3670_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3668_, v___x_3669_);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3679_, lean_object* v_x_3680_, lean_object* v_x_3681_){
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
v___x_3689_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3682_);
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
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3694_, lean_object* v_x_3695_){
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
lean_dec_ref(v_x_3694_);
v___x_3699_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3698_);
return v___x_3699_;
}
else
{
lean_object* v_head_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_inc(v_tail_3697_);
v_head_3700_ = lean_ctor_get(v_x_3694_, 0);
lean_inc(v_head_3700_);
lean_dec_ref(v_x_3694_);
v___x_3701_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3700_);
v___x_3702_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3695_, v___x_3701_, v_tail_3697_);
return v___x_3702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3703_){
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
v___x_3709_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3707_, v___x_3708_);
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
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = lean_unsigned_to_nat(12u);
v___x_3732_ = lean_nat_to_int(v___x_3731_);
return v___x_3732_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = lean_unsigned_to_nat(9u);
v___x_3737_ = lean_nat_to_int(v___x_3736_);
return v___x_3737_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3741_ = lean_unsigned_to_nat(11u);
v___x_3742_ = lean_nat_to_int(v___x_3741_);
return v___x_3742_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3745_ = lean_string_length(v___x_3744_);
return v___x_3745_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3746_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3747_ = lean_nat_to_int(v___x_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3752_){
_start:
{
lean_object* v_numFixed_3753_; lean_object* v_perms_3754_; lean_object* v_revDeps_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v_numFixed_3753_ = lean_ctor_get(v_x_3752_, 0);
lean_inc(v_numFixed_3753_);
v_perms_3754_ = lean_ctor_get(v_x_3752_, 1);
lean_inc_ref(v_perms_3754_);
v_revDeps_3755_ = lean_ctor_get(v_x_3752_, 2);
lean_inc_ref(v_revDeps_3755_);
lean_dec_ref(v_x_3752_);
v___x_3756_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3757_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3758_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3759_ = l_Nat_reprFast(v_numFixed_3753_);
v___x_3760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3758_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = 0;
v___x_3763_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3763_, 0, v___x_3761_);
lean_ctor_set_uint8(v___x_3763_, sizeof(void*)*1, v___x_3762_);
v___x_3764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3757_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3764_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = lean_box(1);
v___x_3768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3766_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3768_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
lean_ctor_set(v___x_3771_, 1, v___x_3756_);
v___x_3772_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3773_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3754_);
v___x_3774_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3775_, 0, v___x_3774_);
lean_ctor_set_uint8(v___x_3775_, sizeof(void*)*1, v___x_3762_);
v___x_3776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3771_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
v___x_3777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
lean_ctor_set(v___x_3777_, 1, v___x_3765_);
v___x_3778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
lean_ctor_set(v___x_3778_, 1, v___x_3767_);
v___x_3779_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3778_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
lean_ctor_set(v___x_3781_, 1, v___x_3756_);
v___x_3782_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3783_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3755_);
v___x_3784_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3785_, 0, v___x_3784_);
lean_ctor_set_uint8(v___x_3785_, sizeof(void*)*1, v___x_3762_);
v___x_3786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3781_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3788_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
lean_ctor_set(v___x_3789_, 1, v___x_3786_);
v___x_3790_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3789_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3787_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
lean_ctor_set_uint8(v___x_3793_, sizeof(void*)*1, v___x_3762_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3794_, lean_object* v_prec_3795_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3794_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3797_, lean_object* v_prec_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3797_, v_prec_3798_);
lean_dec(v_prec_3798_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___f_3808_; lean_object* v___x_5797__overap_3809_; lean_object* v___x_3810_; 
v___f_3808_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_5797__overap_3809_ = lean_panic_fn_borrowed(v___f_3808_, v_msg_3802_);
lean_inc(v___y_3806_);
lean_inc_ref(v___y_3805_);
lean_inc(v___y_3804_);
lean_inc_ref(v___y_3803_);
v___x_3810_ = lean_apply_5(v___x_5797__overap_3809_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, lean_box(0));
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v___f_3824_; lean_object* v___x_5807__overap_3825_; lean_object* v___x_3826_; 
v___f_3824_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_5807__overap_3825_ = lean_panic_fn_borrowed(v___f_3824_, v_msg_3818_);
lean_inc(v___y_3822_);
lean_inc_ref(v___y_3821_);
lean_inc(v___y_3820_);
lean_inc_ref(v___y_3819_);
v___x_3826_ = lean_apply_5(v___x_5807__overap_3825_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, lean_box(0));
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___f_3840_; lean_object* v___x_5817__overap_3841_; lean_object* v___x_3842_; 
v___f_3840_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_5817__overap_3841_ = lean_panic_fn_borrowed(v___f_3840_, v_msg_3834_);
lean_inc(v___y_3838_);
lean_inc_ref(v___y_3837_);
lean_inc(v___y_3836_);
lean_inc_ref(v___y_3835_);
v___x_3842_ = lean_apply_5(v___x_5817__overap_3841_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, lean_box(0));
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
return v_res_3849_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3853_ = lean_unsigned_to_nat(12u);
v___x_3854_ = lean_unsigned_to_nat(294u);
v___x_3855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3856_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_3857_ = l_mkPanicMessageWithDecl(v___x_3856_, v___x_3855_, v___x_3854_, v___x_3853_, v___x_3852_);
return v___x_3857_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3860_ = lean_unsigned_to_nat(12u);
v___x_3861_ = lean_unsigned_to_nat(297u);
v___x_3862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3863_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_3864_ = l_mkPanicMessageWithDecl(v___x_3863_, v___x_3862_, v___x_3861_, v___x_3860_, v___x_3859_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3865_, lean_object* v_as_3866_, size_t v_sz_3867_, size_t v_i_3868_, lean_object* v_b_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_a_3876_; uint8_t v___x_3880_; 
v___x_3880_ = lean_usize_dec_lt(v_i_3868_, v_sz_3867_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; 
v___x_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3881_, 0, v_b_3869_);
return v___x_3881_;
}
else
{
lean_object* v_a_3882_; 
v_a_3882_ = lean_array_uget_borrowed(v_as_3866_, v_i_3868_);
if (lean_obj_tag(v_a_3882_) == 1)
{
lean_object* v_val_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v_val_3883_ = lean_ctor_get(v_a_3882_, 0);
v___x_3884_ = lean_unsigned_to_nat(0u);
v___x_3885_ = lean_box(0);
v___x_3886_ = lean_array_get_borrowed(v___x_3885_, v_val_3883_, v___x_3884_);
if (lean_obj_tag(v___x_3886_) == 1)
{
lean_object* v_val_3887_; lean_object* v___x_3888_; 
v_val_3887_ = lean_ctor_get(v___x_3886_, 0);
v___x_3888_ = lean_array_get_borrowed(v___x_3885_, v___x_3865_, v_val_3887_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
lean_dec_ref(v_b_3869_);
v___x_3889_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3890_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3889_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3900_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3893_ = v___x_3890_;
v_isShared_3894_ = v_isSharedCheck_3900_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3890_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3900_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
if (lean_obj_tag(v_a_3891_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3897_; 
v_a_3895_ = lean_ctor_get(v_a_3891_, 0);
lean_inc(v_a_3895_);
lean_dec_ref(v_a_3891_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v_a_3895_);
v___x_3897_ = v___x_3893_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3895_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
else
{
lean_object* v_a_3899_; 
lean_del_object(v___x_3893_);
v_a_3899_ = lean_ctor_get(v_a_3891_, 0);
lean_inc(v_a_3899_);
lean_dec_ref(v_a_3891_);
v_a_3876_ = v_a_3899_;
goto v___jp_3875_;
}
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
v_a_3901_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3890_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3890_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
else
{
lean_object* v___x_3909_; 
lean_inc_ref(v___x_3888_);
v___x_3909_ = lean_array_push(v_b_3869_, v___x_3888_);
v_a_3876_ = v___x_3909_;
goto v___jp_3875_;
}
}
else
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3910_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3911_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6(v___x_3910_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_dec_ref(v___x_3911_);
v_a_3876_ = v_b_3869_;
goto v___jp_3875_;
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec_ref(v_b_3869_);
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3911_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3911_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
}
else
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = lean_box(0);
v___x_3921_ = lean_array_push(v_b_3869_, v___x_3920_);
v_a_3876_ = v___x_3921_;
goto v___jp_3875_;
}
}
v___jp_3875_:
{
size_t v___x_3877_; size_t v___x_3878_; 
v___x_3877_ = ((size_t)1ULL);
v___x_3878_ = lean_usize_add(v_i_3868_, v___x_3877_);
v_i_3868_ = v___x_3878_;
v_b_3869_ = v_a_3876_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3922_, lean_object* v_as_3923_, lean_object* v_sz_3924_, lean_object* v_i_3925_, lean_object* v_b_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
size_t v_sz_boxed_3932_; size_t v_i_boxed_3933_; lean_object* v_res_3934_; 
v_sz_boxed_3932_ = lean_unbox_usize(v_sz_3924_);
lean_dec(v_sz_3924_);
v_i_boxed_3933_ = lean_unbox_usize(v_i_3925_);
lean_dec(v_i_3925_);
v_res_3934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3922_, v_as_3923_, v_sz_boxed_3932_, v_i_boxed_3933_, v_b_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec_ref(v_as_3923_);
lean_dec_ref(v___x_3922_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3937_, lean_object* v___x_3938_, lean_object* v___x_3939_, lean_object* v_a_3940_, lean_object* v_b_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
uint8_t v___x_3947_; 
v___x_3947_ = lean_nat_dec_lt(v_a_3940_, v_upperBound_3937_);
if (v___x_3947_ == 0)
{
lean_object* v___x_3948_; 
lean_dec(v_a_3940_);
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v_b_3941_);
return v___x_3948_;
}
else
{
lean_object* v___x_3949_; lean_object* v___x_3950_; size_t v_sz_3951_; size_t v___x_3952_; lean_object* v___x_3953_; 
v___x_3949_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3950_ = lean_array_fget_borrowed(v___x_3938_, v_a_3940_);
v_sz_3951_ = lean_array_size(v___x_3950_);
v___x_3952_ = ((size_t)0ULL);
v___x_3953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3939_, v___x_3950_, v_sz_3951_, v___x_3952_, v___x_3949_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref(v___x_3953_);
v___x_3955_ = lean_array_push(v_b_3941_, v_a_3954_);
v___x_3956_ = lean_unsigned_to_nat(1u);
v___x_3957_ = lean_nat_add(v_a_3940_, v___x_3956_);
lean_dec(v_a_3940_);
v_a_3940_ = v___x_3957_;
v_b_3941_ = v___x_3955_;
goto _start;
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
lean_dec_ref(v_b_3941_);
lean_dec(v_a_3940_);
v_a_3959_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3953_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3953_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3967_, lean_object* v___x_3968_, lean_object* v___x_3969_, lean_object* v_a_3970_, lean_object* v_b_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3967_, v___x_3968_, v___x_3969_, v_a_3970_, v_b_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec_ref(v___x_3969_);
lean_dec_ref(v___x_3968_);
lean_dec(v_upperBound_3967_);
return v_res_3977_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3979_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3980_ = lean_unsigned_to_nat(8u);
v___x_3981_ = lean_unsigned_to_nat(281u);
v___x_3982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3983_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_3984_ = l_mkPanicMessageWithDecl(v___x_3983_, v___x_3982_, v___x_3981_, v___x_3980_, v___x_3979_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3985_, lean_object* v_a_3986_, lean_object* v_b_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v_a_3994_; uint8_t v___x_3998_; 
v___x_3998_ = lean_nat_dec_lt(v_a_3986_, v_upperBound_3985_);
if (v___x_3998_ == 0)
{
lean_object* v___x_3999_; 
lean_dec(v_a_3986_);
v___x_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3999_, 0, v_b_3987_);
return v___x_3999_;
}
else
{
lean_object* v_snd_4000_; lean_object* v_snd_4001_; lean_object* v_snd_4002_; lean_object* v_fst_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4127_; 
v_snd_4000_ = lean_ctor_get(v_b_3987_, 1);
lean_inc(v_snd_4000_);
v_snd_4001_ = lean_ctor_get(v_snd_4000_, 1);
lean_inc(v_snd_4001_);
v_snd_4002_ = lean_ctor_get(v_snd_4001_, 1);
lean_inc(v_snd_4002_);
v_fst_4003_ = lean_ctor_get(v_b_3987_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_b_3987_);
if (v_isSharedCheck_4127_ == 0)
{
lean_object* v_unused_4128_; 
v_unused_4128_ = lean_ctor_get(v_b_3987_, 1);
lean_dec(v_unused_4128_);
v___x_4005_ = v_b_3987_;
v_isShared_4006_ = v_isSharedCheck_4127_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_fst_4003_);
lean_dec(v_b_3987_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4127_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v_fst_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4125_; 
v_fst_4007_ = lean_ctor_get(v_snd_4000_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v_snd_4000_);
if (v_isSharedCheck_4125_ == 0)
{
lean_object* v_unused_4126_; 
v_unused_4126_ = lean_ctor_get(v_snd_4000_, 1);
lean_dec(v_unused_4126_);
v___x_4009_ = v_snd_4000_;
v_isShared_4010_ = v_isSharedCheck_4125_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_fst_4007_);
lean_dec(v_snd_4000_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4125_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v_fst_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4123_; 
v_fst_4011_ = lean_ctor_get(v_snd_4001_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v_snd_4001_);
if (v_isSharedCheck_4123_ == 0)
{
lean_object* v_unused_4124_; 
v_unused_4124_ = lean_ctor_get(v_snd_4001_, 1);
lean_dec(v_unused_4124_);
v___x_4013_ = v_snd_4001_;
v_isShared_4014_ = v_isSharedCheck_4123_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_fst_4011_);
lean_dec(v_snd_4001_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4123_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v_array_4015_; lean_object* v_start_4016_; lean_object* v_stop_4017_; uint8_t v___x_4018_; 
v_array_4015_ = lean_ctor_get(v_snd_4002_, 0);
v_start_4016_ = lean_ctor_get(v_snd_4002_, 1);
v_stop_4017_ = lean_ctor_get(v_snd_4002_, 2);
v___x_4018_ = lean_nat_dec_lt(v_start_4016_, v_stop_4017_);
if (v___x_4018_ == 0)
{
lean_object* v___x_4020_; 
lean_dec(v_a_3986_);
if (v_isShared_4014_ == 0)
{
v___x_4020_ = v___x_4013_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_fst_4011_);
lean_ctor_set(v_reuseFailAlloc_4028_, 1, v_snd_4002_);
v___x_4020_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
lean_object* v___x_4022_; 
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 1, v___x_4020_);
v___x_4022_ = v___x_4009_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_fst_4007_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v___x_4020_);
v___x_4022_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
lean_object* v___x_4024_; 
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 1, v___x_4022_);
v___x_4024_ = v___x_4005_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_fst_4003_);
lean_ctor_set(v_reuseFailAlloc_4026_, 1, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
lean_object* v___x_4025_; 
v___x_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
return v___x_4025_;
}
}
}
}
else
{
lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4119_; 
lean_inc(v_stop_4017_);
lean_inc(v_start_4016_);
lean_inc_ref(v_array_4015_);
v_isSharedCheck_4119_ = !lean_is_exclusive(v_snd_4002_);
if (v_isSharedCheck_4119_ == 0)
{
lean_object* v_unused_4120_; lean_object* v_unused_4121_; lean_object* v_unused_4122_; 
v_unused_4120_ = lean_ctor_get(v_snd_4002_, 2);
lean_dec(v_unused_4120_);
v_unused_4121_ = lean_ctor_get(v_snd_4002_, 1);
lean_dec(v_unused_4121_);
v_unused_4122_ = lean_ctor_get(v_snd_4002_, 0);
lean_dec(v_unused_4122_);
v___x_4030_ = v_snd_4002_;
v_isShared_4031_ = v_isSharedCheck_4119_;
goto v_resetjp_4029_;
}
else
{
lean_dec(v_snd_4002_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4119_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v_array_4032_; lean_object* v_start_4033_; lean_object* v_stop_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4039_; 
v_array_4032_ = lean_ctor_get(v_fst_4011_, 0);
v_start_4033_ = lean_ctor_get(v_fst_4011_, 1);
v_stop_4034_ = lean_ctor_get(v_fst_4011_, 2);
v___x_4035_ = lean_array_fget(v_array_4015_, v_start_4016_);
v___x_4036_ = lean_unsigned_to_nat(1u);
v___x_4037_ = lean_nat_add(v_start_4016_, v___x_4036_);
lean_dec(v_start_4016_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v___x_4037_);
v___x_4039_ = v___x_4030_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_array_4015_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v___x_4037_);
lean_ctor_set(v_reuseFailAlloc_4118_, 2, v_stop_4017_);
v___x_4039_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
uint8_t v___x_4040_; 
v___x_4040_ = lean_nat_dec_lt(v_start_4033_, v_stop_4034_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4042_; 
lean_dec(v___x_4035_);
lean_dec(v_a_3986_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 1, v___x_4039_);
v___x_4042_ = v___x_4013_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_fst_4011_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v___x_4039_);
v___x_4042_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
lean_object* v___x_4044_; 
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 1, v___x_4042_);
v___x_4044_ = v___x_4009_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_fst_4007_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
lean_object* v___x_4046_; 
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 1, v___x_4044_);
v___x_4046_ = v___x_4005_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_fst_4003_);
lean_ctor_set(v_reuseFailAlloc_4048_, 1, v___x_4044_);
v___x_4046_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
lean_object* v___x_4047_; 
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
}
}
}
else
{
lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4114_; 
lean_inc(v_stop_4034_);
lean_inc(v_start_4033_);
lean_inc_ref(v_array_4032_);
v_isSharedCheck_4114_ = !lean_is_exclusive(v_fst_4011_);
if (v_isSharedCheck_4114_ == 0)
{
lean_object* v_unused_4115_; lean_object* v_unused_4116_; lean_object* v_unused_4117_; 
v_unused_4115_ = lean_ctor_get(v_fst_4011_, 2);
lean_dec(v_unused_4115_);
v_unused_4116_ = lean_ctor_get(v_fst_4011_, 1);
lean_dec(v_unused_4116_);
v_unused_4117_ = lean_ctor_get(v_fst_4011_, 0);
lean_dec(v_unused_4117_);
v___x_4052_ = v_fst_4011_;
v_isShared_4053_ = v_isSharedCheck_4114_;
goto v_resetjp_4051_;
}
else
{
lean_dec(v_fst_4011_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4114_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4054_; lean_object* v___x_4056_; 
v___x_4054_ = lean_nat_add(v_start_4033_, v___x_4036_);
lean_dec(v_start_4033_);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 1, v___x_4054_);
v___x_4056_ = v___x_4052_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_array_4032_);
lean_ctor_set(v_reuseFailAlloc_4113_, 1, v___x_4054_);
lean_ctor_set(v_reuseFailAlloc_4113_, 2, v_stop_4034_);
v___x_4056_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
if (lean_obj_tag(v___x_4035_) == 1)
{
lean_object* v_val_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4101_; 
v_val_4057_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4059_ = v___x_4035_;
v_isShared_4060_ = v_isSharedCheck_4101_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_val_4057_);
lean_dec(v___x_4035_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4101_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4066_; 
v___x_4061_ = lean_unsigned_to_nat(0u);
v___x_4062_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4063_ = lean_box(0);
v___x_4064_ = lean_array_get(v___x_4063_, v_val_4057_, v___x_4061_);
lean_dec(v_val_4057_);
lean_inc(v_a_3986_);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 0, v_a_3986_);
v___x_4066_ = v___x_4059_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_3986_);
v___x_4066_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
uint8_t v___x_4067_; 
v___x_4067_ = l_Option_instDecidableEq___redArg(v___x_4062_, v___x_4064_, v___x_4066_);
if (v___x_4067_ == 0)
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
lean_dec_ref(v___x_4056_);
lean_dec_ref(v___x_4039_);
lean_del_object(v___x_4013_);
lean_del_object(v___x_4009_);
lean_dec(v_fst_4007_);
lean_del_object(v___x_4005_);
lean_dec(v_fst_4003_);
v___x_4068_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4069_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4068_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4079_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4072_ = v___x_4069_;
v_isShared_4073_ = v_isSharedCheck_4079_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4069_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4079_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
if (lean_obj_tag(v_a_4070_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4076_; 
lean_dec(v_a_3986_);
v_a_4074_ = lean_ctor_get(v_a_4070_, 0);
lean_inc(v_a_4074_);
lean_dec_ref(v_a_4070_);
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 0, v_a_4074_);
v___x_4076_ = v___x_4072_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4074_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
else
{
lean_object* v_a_4078_; 
lean_del_object(v___x_4072_);
v_a_4078_ = lean_ctor_get(v_a_4070_, 0);
lean_inc(v_a_4078_);
lean_dec_ref(v_a_4070_);
v_a_3994_ = v_a_4078_;
goto v___jp_3993_;
}
}
}
else
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4087_; 
lean_dec(v_a_3986_);
v_a_4080_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4082_ = v___x_4069_;
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4069_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4080_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
}
else
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4092_; 
lean_inc(v_fst_4007_);
v___x_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4088_, 0, v_fst_4007_);
v___x_4089_ = lean_array_push(v_fst_4003_, v___x_4088_);
v___x_4090_ = lean_nat_add(v_fst_4007_, v___x_4036_);
lean_dec(v_fst_4007_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 1, v___x_4039_);
lean_ctor_set(v___x_4013_, 0, v___x_4056_);
v___x_4092_ = v___x_4013_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4056_);
lean_ctor_set(v_reuseFailAlloc_4099_, 1, v___x_4039_);
v___x_4092_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
lean_object* v___x_4094_; 
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 1, v___x_4092_);
lean_ctor_set(v___x_4009_, 0, v___x_4090_);
v___x_4094_ = v___x_4009_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4098_, 1, v___x_4092_);
v___x_4094_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
lean_object* v___x_4096_; 
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 1, v___x_4094_);
lean_ctor_set(v___x_4005_, 0, v___x_4089_);
v___x_4096_ = v___x_4005_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v___x_4089_);
lean_ctor_set(v_reuseFailAlloc_4097_, 1, v___x_4094_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
v_a_3994_ = v___x_4096_;
goto v___jp_3993_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4105_; 
lean_dec(v___x_4035_);
v___x_4102_ = lean_box(0);
v___x_4103_ = lean_array_push(v_fst_4003_, v___x_4102_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 1, v___x_4039_);
lean_ctor_set(v___x_4013_, 0, v___x_4056_);
v___x_4105_ = v___x_4013_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4056_);
lean_ctor_set(v_reuseFailAlloc_4112_, 1, v___x_4039_);
v___x_4105_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4107_; 
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 1, v___x_4105_);
v___x_4107_ = v___x_4009_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_fst_4007_);
lean_ctor_set(v_reuseFailAlloc_4111_, 1, v___x_4105_);
v___x_4107_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
lean_object* v___x_4109_; 
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 1, v___x_4107_);
lean_ctor_set(v___x_4005_, 0, v___x_4103_);
v___x_4109_ = v___x_4005_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4103_);
lean_ctor_set(v_reuseFailAlloc_4110_, 1, v___x_4107_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
v_a_3994_ = v___x_4109_;
goto v___jp_3993_;
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
v___jp_3993_:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = lean_unsigned_to_nat(1u);
v___x_3996_ = lean_nat_add(v_a_3986_, v___x_3995_);
lean_dec(v_a_3986_);
v_a_3986_ = v___x_3996_;
v_b_3987_ = v_a_3994_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4129_, lean_object* v_a_4130_, lean_object* v_b_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4129_, v_a_4130_, v_b_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v_upperBound_4129_);
return v_res_4137_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4139_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4140_ = lean_unsigned_to_nat(4u);
v___x_4141_ = lean_unsigned_to_nat(275u);
v___x_4142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4143_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4144_ = l_mkPanicMessageWithDecl(v___x_4143_, v___x_4142_, v___x_4141_, v___x_4140_, v___x_4139_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4145_, lean_object* v___x_4146_, lean_object* v___x_4147_, lean_object* v_xs_4148_, lean_object* v_x_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_graph_4155_; lean_object* v_revDeps_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4209_; 
v_graph_4155_ = lean_ctor_get(v_a_4145_, 0);
v_revDeps_4156_ = lean_ctor_get(v_a_4145_, 1);
v_isSharedCheck_4209_ = !lean_is_exclusive(v_a_4145_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4158_ = v_a_4145_;
v_isShared_4159_ = v_isSharedCheck_4209_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_revDeps_4156_);
lean_inc(v_graph_4155_);
lean_dec(v_a_4145_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4209_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; uint8_t v___x_4163_; 
v___x_4160_ = lean_array_get_borrowed(v___x_4146_, v_graph_4155_, v___x_4147_);
v___x_4161_ = lean_array_get_size(v_xs_4148_);
v___x_4162_ = lean_array_get_size(v___x_4160_);
v___x_4163_ = lean_nat_dec_eq(v___x_4161_, v___x_4162_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; lean_object* v___x_4165_; 
lean_del_object(v___x_4158_);
lean_dec_ref(v_revDeps_4156_);
lean_dec_ref(v_graph_4155_);
lean_dec_ref(v_xs_4148_);
lean_dec(v___x_4147_);
v___x_4164_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4165_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4164_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
return v___x_4165_;
}
else
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4170_; 
v___x_4166_ = lean_mk_empty_array_with_capacity(v___x_4147_);
lean_inc_n(v___x_4147_, 2);
v___x_4167_ = l_Array_toSubarray___redArg(v_xs_4148_, v___x_4147_, v___x_4161_);
lean_inc(v___x_4160_);
v___x_4168_ = l_Array_toSubarray___redArg(v___x_4160_, v___x_4147_, v___x_4162_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 1, v___x_4168_);
lean_ctor_set(v___x_4158_, 0, v___x_4167_);
v___x_4170_ = v___x_4158_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4167_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v___x_4168_);
v___x_4170_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
lean_inc(v___x_4147_);
v___x_4171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4147_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4166_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
v___x_4173_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4161_, v___x_4147_, v___x_4172_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v_snd_4175_; lean_object* v_fst_4176_; lean_object* v_fst_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref(v___x_4173_);
v_snd_4175_ = lean_ctor_get(v_a_4174_, 1);
lean_inc(v_snd_4175_);
v_fst_4176_ = lean_ctor_get(v_a_4174_, 0);
lean_inc_n(v_fst_4176_, 2);
lean_dec(v_a_4174_);
v_fst_4177_ = lean_ctor_get(v_snd_4175_, 0);
lean_inc(v_fst_4177_);
lean_dec(v_snd_4175_);
v___x_4178_ = lean_unsigned_to_nat(1u);
v___x_4179_ = lean_array_get_size(v_graph_4155_);
v___x_4180_ = lean_mk_empty_array_with_capacity(v___x_4178_);
v___x_4181_ = lean_array_push(v___x_4180_, v_fst_4176_);
v___x_4182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4179_, v_graph_4155_, v_fst_4176_, v___x_4178_, v___x_4181_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
lean_dec(v_fst_4176_);
lean_dec_ref(v_graph_4155_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4191_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4185_ = v___x_4182_;
v_isShared_4186_ = v_isSharedCheck_4191_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4182_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4191_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4189_; 
v___x_4187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4187_, 0, v_fst_4177_);
lean_ctor_set(v___x_4187_, 1, v_a_4183_);
lean_ctor_set(v___x_4187_, 2, v_revDeps_4156_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 0, v___x_4187_);
v___x_4189_ = v___x_4185_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4187_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
else
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
lean_dec(v_fst_4177_);
lean_dec_ref(v_revDeps_4156_);
v_a_4192_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4194_ = v___x_4182_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4182_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_dec_ref(v_revDeps_4156_);
lean_dec_ref(v_graph_4155_);
v_a_4200_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4173_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4173_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4210_, lean_object* v___x_4211_, lean_object* v___x_4212_, lean_object* v_xs_4213_, lean_object* v_x_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4210_, v___x_4211_, v___x_4212_, v_xs_4213_, v_x_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec_ref(v_x_4214_);
lean_dec_ref(v___x_4211_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_){
_start:
{
lean_object* v___x_4227_; 
lean_inc_ref(v_preDefs_4221_);
v___x_4227_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4221_, v_a_4222_, v_a_4223_, v_a_4224_, v_a_4225_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v_value_4232_; lean_object* v___x_4233_; lean_object* v___f_4234_; uint8_t v___x_4235_; lean_object* v___x_4236_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref(v___x_4227_);
v___x_4229_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4230_ = lean_unsigned_to_nat(0u);
v___x_4231_ = lean_array_get(v___x_4229_, v_preDefs_4221_, v___x_4230_);
lean_dec_ref(v_preDefs_4221_);
v_value_4232_ = lean_ctor_get(v___x_4231_, 7);
lean_inc_ref(v_value_4232_);
lean_dec(v___x_4231_);
v___x_4233_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4234_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4234_, 0, v_a_4228_);
lean_closure_set(v___f_4234_, 1, v___x_4233_);
lean_closure_set(v___f_4234_, 2, v___x_4230_);
v___x_4235_ = 0;
v___x_4236_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4232_, v___f_4234_, v___x_4235_, v_a_4222_, v_a_4223_, v_a_4224_, v_a_4225_);
return v___x_4236_;
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec_ref(v_preDefs_4221_);
v_a_4237_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4227_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4227_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
lean_dec(v_a_4249_);
lean_dec_ref(v_a_4248_);
lean_dec(v_a_4247_);
lean_dec_ref(v_a_4246_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4252_, lean_object* v___x_4253_, lean_object* v___x_4254_, lean_object* v_inst_4255_, lean_object* v_R_4256_, lean_object* v_a_4257_, lean_object* v_b_4258_, lean_object* v_c_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v___x_4265_; 
v___x_4265_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4252_, v___x_4253_, v___x_4254_, v_a_4257_, v_b_4258_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4266_, lean_object* v___x_4267_, lean_object* v___x_4268_, lean_object* v_inst_4269_, lean_object* v_R_4270_, lean_object* v_a_4271_, lean_object* v_b_4272_, lean_object* v_c_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4266_, v___x_4267_, v___x_4268_, v_inst_4269_, v_R_4270_, v_a_4271_, v_b_4272_, v_c_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec_ref(v___x_4268_);
lean_dec_ref(v___x_4267_);
lean_dec(v_upperBound_4266_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4280_, lean_object* v_inst_4281_, lean_object* v_R_4282_, lean_object* v_a_4283_, lean_object* v_b_4284_, lean_object* v_c_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4280_, v_a_4283_, v_b_4284_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4292_, lean_object* v_inst_4293_, lean_object* v_R_4294_, lean_object* v_a_4295_, lean_object* v_b_4296_, lean_object* v_c_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4292_, v_inst_4293_, v_R_4294_, v_a_4295_, v_b_4296_, v_c_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec(v_upperBound_4292_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4304_, size_t v_i_4305_, size_t v_stop_4306_, lean_object* v_b_4307_){
_start:
{
uint8_t v___x_4308_; 
v___x_4308_ = lean_usize_dec_eq(v_i_4305_, v_stop_4306_);
if (v___x_4308_ == 0)
{
size_t v___x_4309_; size_t v___x_4310_; lean_object* v___x_4311_; 
v___x_4309_ = ((size_t)1ULL);
v___x_4310_ = lean_usize_sub(v_i_4305_, v___x_4309_);
v___x_4311_ = lean_array_uget_borrowed(v_as_4304_, v___x_4310_);
if (lean_obj_tag(v___x_4311_) == 0)
{
v_i_4305_ = v___x_4310_;
goto _start;
}
else
{
lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4313_ = lean_unsigned_to_nat(1u);
v___x_4314_ = lean_nat_add(v_b_4307_, v___x_4313_);
lean_dec(v_b_4307_);
v_i_4305_ = v___x_4310_;
v_b_4307_ = v___x_4314_;
goto _start;
}
}
else
{
return v_b_4307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4316_, lean_object* v_i_4317_, lean_object* v_stop_4318_, lean_object* v_b_4319_){
_start:
{
size_t v_i_boxed_4320_; size_t v_stop_boxed_4321_; lean_object* v_res_4322_; 
v_i_boxed_4320_ = lean_unbox_usize(v_i_4317_);
lean_dec(v_i_4317_);
v_stop_boxed_4321_ = lean_unbox_usize(v_stop_4318_);
lean_dec(v_stop_4318_);
v_res_4322_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4316_, v_i_boxed_4320_, v_stop_boxed_4321_, v_b_4319_);
lean_dec_ref(v_as_4316_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4323_){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4324_ = lean_unsigned_to_nat(0u);
v___x_4325_ = lean_array_get_size(v_perm_4323_);
v___x_4326_ = lean_nat_dec_lt(v___x_4324_, v___x_4325_);
if (v___x_4326_ == 0)
{
return v___x_4324_;
}
else
{
size_t v___x_4327_; size_t v___x_4328_; lean_object* v___x_4329_; 
v___x_4327_ = lean_usize_of_nat(v___x_4325_);
v___x_4328_ = ((size_t)0ULL);
v___x_4329_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4323_, v___x_4327_, v___x_4328_, v___x_4324_);
return v___x_4329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4330_);
lean_dec_ref(v_perm_4330_);
return v_res_4331_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4332_, lean_object* v_i_4333_){
_start:
{
lean_object* v___x_4334_; uint8_t v___x_4335_; 
v___x_4334_ = lean_array_get_size(v_perm_4332_);
v___x_4335_ = lean_nat_dec_lt(v_i_4333_, v___x_4334_);
if (v___x_4335_ == 0)
{
return v___x_4335_;
}
else
{
lean_object* v___x_4336_; 
v___x_4336_ = lean_array_fget_borrowed(v_perm_4332_, v_i_4333_);
if (lean_obj_tag(v___x_4336_) == 0)
{
uint8_t v___x_4337_; 
v___x_4337_ = 0;
return v___x_4337_;
}
else
{
return v___x_4335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4338_, lean_object* v_i_4339_){
_start:
{
uint8_t v_res_4340_; lean_object* v_r_4341_; 
v_res_4340_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4338_, v_i_4339_);
lean_dec(v_i_4339_);
lean_dec_ref(v_perm_4338_);
v_r_4341_ = lean_box(v_res_4340_);
return v_r_4341_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
lean_object* v___f_4348_; lean_object* v___x_1076__overap_4349_; lean_object* v___x_4350_; 
v___f_4348_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_1076__overap_4349_ = lean_panic_fn_borrowed(v___f_4348_, v_msg_4342_);
lean_inc(v___y_4346_);
lean_inc_ref(v___y_4345_);
lean_inc(v___y_4344_);
lean_inc_ref(v___y_4343_);
v___x_4350_ = lean_apply_5(v___x_1076__overap_4349_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, lean_box(0));
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4358_, lean_object* v_msg_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_){
_start:
{
lean_object* v___x_4365_; 
v___x_4365_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4366_, lean_object* v_msg_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4366_, v_msg_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4374_, lean_object* v_maxFVars_x3f_4375_, lean_object* v_k_4376_, uint8_t v_cleanupAnnotations_4377_, uint8_t v_whnfType_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v___f_4384_; lean_object* v___x_4385_; 
v___f_4384_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4384_, 0, v_k_4376_);
v___x_4385_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4374_, v_maxFVars_x3f_4375_, v___f_4384_, v_cleanupAnnotations_4377_, v_whnfType_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4385_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4385_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
else
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4401_; 
v_a_4394_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4396_ = v___x_4385_;
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4385_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4402_, lean_object* v_maxFVars_x3f_4403_, lean_object* v_k_4404_, lean_object* v_cleanupAnnotations_4405_, lean_object* v_whnfType_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4412_; uint8_t v_whnfType_boxed_4413_; lean_object* v_res_4414_; 
v_cleanupAnnotations_boxed_4412_ = lean_unbox(v_cleanupAnnotations_4405_);
v_whnfType_boxed_4413_ = lean_unbox(v_whnfType_4406_);
v_res_4414_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4402_, v_maxFVars_x3f_4403_, v_k_4404_, v_cleanupAnnotations_boxed_4412_, v_whnfType_boxed_4413_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4415_, lean_object* v_type_4416_, lean_object* v_maxFVars_x3f_4417_, lean_object* v_k_4418_, uint8_t v_cleanupAnnotations_4419_, uint8_t v_whnfType_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4416_, v_maxFVars_x3f_4417_, v_k_4418_, v_cleanupAnnotations_4419_, v_whnfType_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4427_, lean_object* v_type_4428_, lean_object* v_maxFVars_x3f_4429_, lean_object* v_k_4430_, lean_object* v_cleanupAnnotations_4431_, lean_object* v_whnfType_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4438_; uint8_t v_whnfType_boxed_4439_; lean_object* v_res_4440_; 
v_cleanupAnnotations_boxed_4438_ = lean_unbox(v_cleanupAnnotations_4431_);
v_whnfType_boxed_4439_ = lean_unbox(v_whnfType_4432_);
v_res_4440_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4427_, v_type_4428_, v_maxFVars_x3f_4429_, v_k_4430_, v_cleanupAnnotations_boxed_4438_, v_whnfType_boxed_4439_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
return v_res_4440_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4443_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4444_ = lean_unsigned_to_nat(6u);
v___x_4445_ = lean_unsigned_to_nat(329u);
v___x_4446_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4447_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4448_ = l_mkPanicMessageWithDecl(v___x_4447_, v___x_4446_, v___x_4445_, v___x_4444_, v___x_4443_);
return v___x_4448_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4452_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4453_ = lean_unsigned_to_nat(8u);
v___x_4454_ = lean_unsigned_to_nat(322u);
v___x_4455_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4456_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4457_ = l_mkPanicMessageWithDecl(v___x_4456_, v___x_4455_, v___x_4454_, v___x_4453_, v___x_4452_);
return v___x_4457_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___x_4459_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4460_ = lean_unsigned_to_nat(8u);
v___x_4461_ = lean_unsigned_to_nat(325u);
v___x_4462_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4463_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4464_ = l_mkPanicMessageWithDecl(v___x_4463_, v___x_4462_, v___x_4461_, v___x_4460_, v___x_4459_);
return v___x_4464_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4466_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4467_ = lean_unsigned_to_nat(8u);
v___x_4468_ = lean_unsigned_to_nat(324u);
v___x_4469_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4470_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4471_ = l_mkPanicMessageWithDecl(v___x_4470_, v___x_4469_, v___x_4468_, v___x_4467_, v___x_4466_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4472_, lean_object* v_xs_4473_, lean_object* v_val_4474_, lean_object* v_i_4475_, lean_object* v_perm_4476_, lean_object* v_k_4477_, lean_object* v_xs_x27_4478_, lean_object* v_type_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v___x_4485_; uint8_t v___x_4486_; 
v___x_4485_ = lean_array_get_size(v_xs_x27_4478_);
v___x_4486_ = lean_nat_dec_eq(v___x_4485_, v___x_4472_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
lean_dec_ref(v_type_4479_);
lean_dec_ref(v_k_4477_);
lean_dec_ref(v_perm_4476_);
lean_dec_ref(v_xs_4473_);
v___x_4487_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4488_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4487_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
return v___x_4488_;
}
else
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v_x_4491_; lean_object* v___x_4492_; 
v___x_4489_ = l_Lean_instInhabitedExpr;
v___x_4490_ = lean_unsigned_to_nat(0u);
v_x_4491_ = lean_array_get_borrowed(v___x_4489_, v_xs_x27_4478_, v___x_4490_);
lean_inc(v___y_4483_);
lean_inc_ref(v___y_4482_);
lean_inc(v___y_4481_);
lean_inc_ref(v___y_4480_);
lean_inc(v_x_4491_);
v___x_4492_ = lean_infer_type(v_x_4491_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v_a_4493_; uint8_t v___x_4494_; 
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
lean_inc(v_a_4493_);
lean_dec_ref(v___x_4492_);
v___x_4494_ = l_Lean_Expr_hasLooseBVars(v_a_4493_);
lean_dec(v_a_4493_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4495_; uint8_t v___x_4496_; 
v___x_4495_ = lean_array_get_size(v_xs_4473_);
v___x_4496_ = lean_nat_dec_lt(v_val_4474_, v___x_4495_);
if (v___x_4496_ == 0)
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
lean_dec_ref(v_type_4479_);
lean_dec_ref(v_k_4477_);
lean_dec_ref(v_perm_4476_);
lean_dec_ref(v_xs_4473_);
v___x_4497_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4498_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4497_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
return v___x_4498_;
}
else
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4499_ = lean_nat_add(v_i_4475_, v___x_4472_);
lean_inc(v_x_4491_);
v___x_4500_ = lean_array_set(v_xs_4473_, v_val_4474_, v_x_4491_);
v___x_4501_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4476_, v_k_4477_, v___x_4499_, v_type_4479_, v___x_4500_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
return v___x_4501_;
}
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
lean_dec_ref(v_type_4479_);
lean_dec_ref(v_k_4477_);
lean_dec_ref(v_perm_4476_);
lean_dec_ref(v_xs_4473_);
v___x_4502_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4503_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4502_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
return v___x_4503_;
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec_ref(v_type_4479_);
lean_dec_ref(v_k_4477_);
lean_dec_ref(v_perm_4476_);
lean_dec_ref(v_xs_4473_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4512_, lean_object* v_xs_4513_, lean_object* v_val_4514_, lean_object* v_i_4515_, lean_object* v_perm_4516_, lean_object* v_k_4517_, lean_object* v_xs_x27_4518_, lean_object* v_type_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4512_, v_xs_4513_, v_val_4514_, v_i_4515_, v_perm_4516_, v_k_4517_, v_xs_x27_4518_, v_type_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec_ref(v_xs_x27_4518_);
lean_dec(v_i_4515_);
lean_dec(v_val_4514_);
lean_dec(v___x_4512_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4526_, lean_object* v_k_4527_, lean_object* v_i_4528_, lean_object* v_type_4529_, lean_object* v_xs_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v___x_4536_; uint8_t v___x_4537_; 
v___x_4536_ = lean_array_get_size(v_perm_4526_);
v___x_4537_ = lean_nat_dec_lt(v_i_4528_, v___x_4536_);
if (v___x_4537_ == 0)
{
lean_object* v___x_4538_; 
lean_dec_ref(v_type_4529_);
lean_dec(v_i_4528_);
lean_dec_ref(v_perm_4526_);
lean_inc(v_a_4534_);
lean_inc_ref(v_a_4533_);
lean_inc(v_a_4532_);
lean_inc_ref(v_a_4531_);
v___x_4538_ = lean_apply_6(v_k_4527_, v_xs_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, lean_box(0));
return v___x_4538_;
}
else
{
lean_object* v___x_4539_; 
v___x_4539_ = lean_array_fget_borrowed(v_perm_4526_, v_i_4528_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v___x_4540_; 
lean_inc(v_a_4534_);
lean_inc_ref(v_a_4533_);
lean_inc(v_a_4532_);
lean_inc_ref(v_a_4531_);
v___x_4540_ = lean_whnf(v_type_4529_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; uint8_t v___x_4542_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
lean_inc(v_a_4541_);
lean_dec_ref(v___x_4540_);
v___x_4542_ = l_Lean_Expr_isForall(v_a_4541_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; lean_object* v___x_4544_; 
lean_dec(v_a_4541_);
lean_dec_ref(v_xs_4530_);
lean_dec(v_i_4528_);
lean_dec_ref(v_k_4527_);
lean_dec_ref(v_perm_4526_);
v___x_4543_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4544_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4543_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
return v___x_4544_;
}
else
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4545_ = lean_unsigned_to_nat(1u);
v___x_4546_ = lean_nat_add(v_i_4528_, v___x_4545_);
lean_dec(v_i_4528_);
v___x_4547_ = l_Lean_Expr_bindingBody_x21(v_a_4541_);
lean_dec(v_a_4541_);
v_i_4528_ = v___x_4546_;
v_type_4529_ = v___x_4547_;
goto _start;
}
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_dec_ref(v_xs_4530_);
lean_dec(v_i_4528_);
lean_dec_ref(v_k_4527_);
lean_dec_ref(v_perm_4526_);
v_a_4549_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4540_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4540_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
else
{
lean_object* v_val_4557_; lean_object* v___x_4558_; lean_object* v___f_4559_; lean_object* v___x_4560_; uint8_t v___x_4561_; lean_object* v___x_4562_; 
v_val_4557_ = lean_ctor_get(v___x_4539_, 0);
lean_inc(v_val_4557_);
v___x_4558_ = lean_unsigned_to_nat(1u);
v___f_4559_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4559_, 0, v___x_4558_);
lean_closure_set(v___f_4559_, 1, v_xs_4530_);
lean_closure_set(v___f_4559_, 2, v_val_4557_);
lean_closure_set(v___f_4559_, 3, v_i_4528_);
lean_closure_set(v___f_4559_, 4, v_perm_4526_);
lean_closure_set(v___f_4559_, 5, v_k_4527_);
v___x_4560_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4561_ = 0;
v___x_4562_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4529_, v___x_4560_, v___f_4559_, v___x_4537_, v___x_4561_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
return v___x_4562_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4563_, lean_object* v_k_4564_, lean_object* v_i_4565_, lean_object* v_type_4566_, lean_object* v_xs_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4563_, v_k_4564_, v_i_4565_, v_type_4566_, v_xs_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
lean_dec(v_a_4571_);
lean_dec_ref(v_a_4570_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4574_, lean_object* v_perm_4575_, lean_object* v_k_4576_, lean_object* v_i_4577_, lean_object* v_type_4578_, lean_object* v_xs_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_){
_start:
{
lean_object* v___x_4585_; 
v___x_4585_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4575_, v_k_4576_, v_i_4577_, v_type_4578_, v_xs_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4586_, lean_object* v_perm_4587_, lean_object* v_k_4588_, lean_object* v_i_4589_, lean_object* v_type_4590_, lean_object* v_xs_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4586_, v_perm_4587_, v_k_4588_, v_i_4589_, v_type_4590_, v_xs_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_);
lean_dec(v_a_4595_);
lean_dec_ref(v_a_4594_);
lean_dec(v_a_4593_);
lean_dec_ref(v_a_4592_);
return v_res_4597_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = lean_unsigned_to_nat(0u);
v___x_4599_ = l_Lean_Level_ofNat(v___x_4598_);
return v___x_4599_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4600_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4601_ = l_Lean_mkSort(v___x_4600_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4602_, lean_object* v_type_4603_, lean_object* v_k_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4610_ = lean_unsigned_to_nat(0u);
v___x_4611_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4602_);
v___x_4612_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4613_ = lean_mk_array(v___x_4611_, v___x_4612_);
v___x_4614_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4602_, v_k_4604_, v___x_4610_, v_type_4603_, v___x_4613_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
return v___x_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4615_, lean_object* v_type_4616_, lean_object* v_k_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4615_, v_type_4616_, v_k_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_);
lean_dec(v_a_4621_);
lean_dec_ref(v_a_4620_);
lean_dec(v_a_4619_);
lean_dec_ref(v_a_4618_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4624_, lean_object* v_perm_4625_, lean_object* v_type_4626_, lean_object* v_k_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_){
_start:
{
lean_object* v___x_4633_; 
v___x_4633_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4625_, v_type_4626_, v_k_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4634_, lean_object* v_perm_4635_, lean_object* v_type_4636_, lean_object* v_k_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_){
_start:
{
lean_object* v_res_4643_; 
v_res_4643_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4634_, v_perm_4635_, v_type_4636_, v_k_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_);
lean_dec(v_a_4641_);
lean_dec_ref(v_a_4640_);
lean_dec(v_a_4639_);
lean_dec_ref(v_a_4638_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4644_, lean_object* v_runInBase_4645_, lean_object* v_b_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4652_ = lean_apply_1(v_k_4644_, v_b_4646_);
lean_inc(v___y_4650_);
lean_inc_ref(v___y_4649_);
lean_inc(v___y_4648_);
lean_inc_ref(v___y_4647_);
v___x_4653_ = lean_apply_7(v_runInBase_4645_, lean_box(0), v___x_4652_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_, lean_box(0));
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4654_, lean_object* v_runInBase_4655_, lean_object* v_b_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4654_, v_runInBase_4655_, v_b_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4663_, lean_object* v_perm_4664_, lean_object* v_type_4665_, lean_object* v_runInBase_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v___f_4672_; lean_object* v___x_4673_; 
v___f_4672_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4672_, 0, v_k_4663_);
lean_closure_set(v___f_4672_, 1, v_runInBase_4666_);
v___x_4673_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4664_, v_type_4665_, v___f_4672_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4674_, lean_object* v_perm_4675_, lean_object* v_type_4676_, lean_object* v_runInBase_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4674_, v_perm_4675_, v_type_4676_, v_runInBase_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4684_, lean_object* v_inst_4685_, lean_object* v_perm_4686_, lean_object* v_type_4687_, lean_object* v_k_4688_){
_start:
{
lean_object* v_toBind_4689_; lean_object* v_liftWith_4690_; lean_object* v_restoreM_4691_; lean_object* v___f_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v_toBind_4689_ = lean_ctor_get(v_inst_4685_, 1);
lean_inc(v_toBind_4689_);
lean_dec_ref(v_inst_4685_);
v_liftWith_4690_ = lean_ctor_get(v_inst_4684_, 0);
lean_inc(v_liftWith_4690_);
v_restoreM_4691_ = lean_ctor_get(v_inst_4684_, 1);
lean_inc(v_restoreM_4691_);
lean_dec_ref(v_inst_4684_);
v___f_4692_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4692_, 0, v_k_4688_);
lean_closure_set(v___f_4692_, 1, v_perm_4686_);
lean_closure_set(v___f_4692_, 2, v_type_4687_);
v___x_4693_ = lean_apply_2(v_liftWith_4690_, lean_box(0), v___f_4692_);
v___x_4694_ = lean_apply_1(v_restoreM_4691_, lean_box(0));
v___x_4695_ = lean_apply_4(v_toBind_4689_, lean_box(0), lean_box(0), v___x_4693_, v___x_4694_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4696_, lean_object* v_00_u03b1_4697_, lean_object* v_inst_4698_, lean_object* v_inst_4699_, lean_object* v_perm_4700_, lean_object* v_type_4701_, lean_object* v_k_4702_){
_start:
{
lean_object* v___x_4703_; 
v___x_4703_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4698_, v_inst_4699_, v_perm_4700_, v_type_4701_, v_k_4702_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v___f_4710_; lean_object* v___x_603__overap_4711_; lean_object* v___x_4712_; 
v___f_4710_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_603__overap_4711_ = lean_panic_fn_borrowed(v___f_4710_, v_msg_4704_);
lean_inc(v___y_4708_);
lean_inc_ref(v___y_4707_);
lean_inc(v___y_4706_);
lean_inc_ref(v___y_4705_);
v___x_4712_ = lean_apply_5(v___x_603__overap_4711_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, lean_box(0));
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
lean_object* v_res_4719_; 
v_res_4719_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
return v_res_4719_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4722_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4723_ = lean_unsigned_to_nat(10u);
v___x_4724_ = lean_unsigned_to_nat(353u);
v___x_4725_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4726_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4727_ = l_mkPanicMessageWithDecl(v___x_4726_, v___x_4725_, v___x_4724_, v___x_4723_, v___x_4722_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4728_, lean_object* v_xs_4729_, lean_object* v_tail_4730_, lean_object* v_ys_4731_, lean_object* v_type_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
lean_object* v_res_4738_; 
v_res_4738_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4728_, v_xs_4729_, v_tail_4730_, v_ys_4731_, v_type_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec_ref(v_ys_4731_);
lean_dec(v___x_4728_);
return v_res_4738_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4739_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4740_ = lean_unsigned_to_nat(8u);
v___x_4741_ = lean_unsigned_to_nat(349u);
v___x_4742_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4743_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4744_ = l_mkPanicMessageWithDecl(v___x_4743_, v___x_4742_, v___x_4741_, v___x_4740_, v___x_4739_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4745_, lean_object* v_x_4746_, lean_object* v_x_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_){
_start:
{
if (lean_obj_tag(v_x_4746_) == 0)
{
lean_object* v___x_4753_; 
lean_dec_ref(v_xs_4745_);
v___x_4753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4753_, 0, v_x_4747_);
return v___x_4753_;
}
else
{
lean_object* v_head_4754_; 
v_head_4754_ = lean_ctor_get(v_x_4746_, 0);
if (lean_obj_tag(v_head_4754_) == 0)
{
lean_object* v_tail_4755_; lean_object* v___x_4756_; lean_object* v___f_4757_; lean_object* v___x_4758_; uint8_t v___x_4759_; lean_object* v___x_4760_; 
v_tail_4755_ = lean_ctor_get(v_x_4746_, 1);
lean_inc(v_tail_4755_);
lean_dec_ref(v_x_4746_);
v___x_4756_ = lean_unsigned_to_nat(1u);
v___f_4757_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4757_, 0, v___x_4756_);
lean_closure_set(v___f_4757_, 1, v_xs_4745_);
lean_closure_set(v___f_4757_, 2, v_tail_4755_);
v___x_4758_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4759_ = 0;
v___x_4760_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4747_, v___x_4758_, v___f_4757_, v___x_4759_, v___x_4759_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_);
return v___x_4760_;
}
else
{
lean_object* v_tail_4761_; lean_object* v_val_4762_; lean_object* v___x_4763_; uint8_t v___x_4764_; 
lean_inc_ref(v_head_4754_);
v_tail_4761_ = lean_ctor_get(v_x_4746_, 1);
lean_inc(v_tail_4761_);
lean_dec_ref(v_x_4746_);
v_val_4762_ = lean_ctor_get(v_head_4754_, 0);
lean_inc(v_val_4762_);
lean_dec_ref(v_head_4754_);
v___x_4763_ = lean_array_get_size(v_xs_4745_);
v___x_4764_ = lean_nat_dec_lt(v_val_4762_, v___x_4763_);
if (v___x_4764_ == 0)
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
lean_dec(v_val_4762_);
lean_dec(v_tail_4761_);
lean_dec_ref(v_x_4747_);
lean_dec_ref(v_xs_4745_);
v___x_4765_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4766_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4765_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_);
return v___x_4766_;
}
else
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4767_ = l_Lean_instInhabitedExpr;
v___x_4768_ = lean_array_get_borrowed(v___x_4767_, v_xs_4745_, v_val_4762_);
lean_dec(v_val_4762_);
v___x_4769_ = lean_unsigned_to_nat(1u);
v___x_4770_ = lean_mk_empty_array_with_capacity(v___x_4769_);
lean_inc(v___x_4768_);
v___x_4771_ = lean_array_push(v___x_4770_, v___x_4768_);
v___x_4772_ = l_Lean_Meta_instantiateForall(v_x_4747_, v___x_4771_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_);
lean_dec_ref(v___x_4771_);
if (lean_obj_tag(v___x_4772_) == 0)
{
lean_object* v_a_4773_; 
v_a_4773_ = lean_ctor_get(v___x_4772_, 0);
lean_inc(v_a_4773_);
lean_dec_ref(v___x_4772_);
v_x_4746_ = v_tail_4761_;
v_x_4747_ = v_a_4773_;
goto _start;
}
else
{
lean_dec(v_tail_4761_);
lean_dec_ref(v_xs_4745_);
return v___x_4772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4775_, lean_object* v_xs_4776_, lean_object* v_tail_4777_, lean_object* v_ys_4778_, lean_object* v_type_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_){
_start:
{
lean_object* v___x_4785_; uint8_t v___x_4786_; 
v___x_4785_ = lean_array_get_size(v_ys_4778_);
v___x_4786_ = lean_nat_dec_eq(v___x_4785_, v___x_4775_);
if (v___x_4786_ == 0)
{
lean_object* v___x_4787_; lean_object* v___x_4788_; 
lean_dec_ref(v_type_4779_);
lean_dec(v_tail_4777_);
lean_dec_ref(v_xs_4776_);
v___x_4787_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4788_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4787_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
return v___x_4788_;
}
else
{
lean_object* v___x_4789_; 
v___x_4789_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4776_, v_tail_4777_, v_type_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4790_; uint8_t v___x_4791_; uint8_t v___x_4792_; lean_object* v___x_4793_; 
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
lean_inc(v_a_4790_);
lean_dec_ref(v___x_4789_);
v___x_4791_ = 0;
v___x_4792_ = 1;
v___x_4793_ = l_Lean_Meta_mkForallFVars(v_ys_4778_, v_a_4790_, v___x_4791_, v___x_4786_, v___x_4786_, v___x_4792_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
return v___x_4793_;
}
else
{
return v___x_4789_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4794_, lean_object* v_x_4795_, lean_object* v_x_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4794_, v_x_4795_, v_x_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
return v_res_4802_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4805_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4806_ = lean_unsigned_to_nat(2u);
v___x_4807_ = lean_unsigned_to_nat(343u);
v___x_4808_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4809_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4810_ = l_mkPanicMessageWithDecl(v___x_4809_, v___x_4808_, v___x_4807_, v___x_4806_, v___x_4805_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4811_, lean_object* v_type_u2080_4812_, lean_object* v_xs_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_){
_start:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; uint8_t v___x_4821_; 
v___x_4819_ = lean_array_get_size(v_xs_4813_);
v___x_4820_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4811_);
v___x_4821_ = lean_nat_dec_eq(v___x_4819_, v___x_4820_);
lean_dec(v___x_4820_);
if (v___x_4821_ == 0)
{
lean_object* v___x_4822_; lean_object* v___x_4823_; 
lean_dec_ref(v_xs_4813_);
lean_dec_ref(v_type_u2080_4812_);
lean_dec_ref(v_perm_4811_);
v___x_4822_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4823_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4822_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_);
return v___x_4823_;
}
else
{
lean_object* v_mask_4824_; lean_object* v___x_4825_; 
v_mask_4824_ = lean_array_to_list(v_perm_4811_);
v___x_4825_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4813_, v_mask_4824_, v_type_u2080_4812_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_);
return v___x_4825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4826_, lean_object* v_type_u2080_4827_, lean_object* v_xs_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4826_, v_type_u2080_4827_, v_xs_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_);
lean_dec(v_a_4832_);
lean_dec_ref(v_a_4831_);
lean_dec(v_a_4830_);
lean_dec_ref(v_a_4829_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(lean_object* v_e_4835_, lean_object* v_maxFVars_4836_, lean_object* v_k_4837_, uint8_t v_cleanupAnnotations_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_){
_start:
{
lean_object* v___f_4844_; uint8_t v___x_4845_; uint8_t v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___f_4844_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4844_, 0, v_k_4837_);
v___x_4845_ = 1;
v___x_4846_ = 0;
v___x_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4847_, 0, v_maxFVars_4836_);
v___x_4848_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4835_, v___x_4845_, v___x_4846_, v___x_4845_, v___x_4846_, v___x_4847_, v___f_4844_, v_cleanupAnnotations_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
lean_dec_ref(v___x_4847_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4856_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4851_ = v___x_4848_;
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4848_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4854_; 
if (v_isShared_4852_ == 0)
{
v___x_4854_ = v___x_4851_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
return v___x_4854_;
}
}
}
else
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
v_a_4857_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4859_ = v___x_4848_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4848_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg___boxed(lean_object* v_e_4865_, lean_object* v_maxFVars_4866_, lean_object* v_k_4867_, lean_object* v_cleanupAnnotations_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4874_; lean_object* v_res_4875_; 
v_cleanupAnnotations_boxed_4874_ = lean_unbox(v_cleanupAnnotations_4868_);
v_res_4875_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(v_e_4865_, v_maxFVars_4866_, v_k_4867_, v_cleanupAnnotations_boxed_4874_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec(v___y_4870_);
lean_dec_ref(v___y_4869_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_00_u03b1_4876_, lean_object* v_e_4877_, lean_object* v_maxFVars_4878_, lean_object* v_k_4879_, uint8_t v_cleanupAnnotations_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_){
_start:
{
lean_object* v___x_4886_; 
v___x_4886_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(v_e_4877_, v_maxFVars_4878_, v_k_4879_, v_cleanupAnnotations_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_00_u03b1_4887_, lean_object* v_e_4888_, lean_object* v_maxFVars_4889_, lean_object* v_k_4890_, lean_object* v_cleanupAnnotations_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4897_; lean_object* v_res_4898_; 
v_cleanupAnnotations_boxed_4897_ = lean_unbox(v_cleanupAnnotations_4891_);
v_res_4898_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_00_u03b1_4887_, v_e_4888_, v_maxFVars_4889_, v_k_4890_, v_cleanupAnnotations_boxed_4897_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
return v_res_4898_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___y_4899_){
_start:
{
if (lean_obj_tag(v___y_4899_) == 0)
{
uint8_t v___x_4900_; 
v___x_4900_ = 1;
return v___x_4900_;
}
else
{
uint8_t v___x_4901_; 
v___x_4901_ = 0;
return v___x_4901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___y_4902_){
_start:
{
uint8_t v_res_4903_; lean_object* v_r_4904_; 
v_res_4903_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___y_4902_);
lean_dec(v___y_4902_);
v_r_4904_ = lean_box(v_res_4903_);
return v_r_4904_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2(void){
_start:
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4907_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__1));
v___x_4908_ = lean_unsigned_to_nat(12u);
v___x_4909_ = lean_unsigned_to_nat(376u);
v___x_4910_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__0));
v___x_4911_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4912_ = l_mkPanicMessageWithDecl(v___x_4911_, v___x_4910_, v___x_4909_, v___x_4908_, v___x_4907_);
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___boxed(lean_object* v___x_4914_, lean_object* v_xs_4915_, lean_object* v_tail_4916_, lean_object* v___x_4917_, lean_object* v___x_4918_, lean_object* v_ys_4919_, lean_object* v_value_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
uint8_t v___x_1280__boxed_4926_; uint8_t v___x_1281__boxed_4927_; lean_object* v_res_4928_; 
v___x_1280__boxed_4926_ = lean_unbox(v___x_4917_);
v___x_1281__boxed_4927_ = lean_unbox(v___x_4918_);
v_res_4928_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1(v___x_4914_, v_xs_4915_, v_tail_4916_, v___x_1280__boxed_4926_, v___x_1281__boxed_4927_, v_ys_4919_, v_value_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_);
lean_dec(v___y_4924_);
lean_dec_ref(v___y_4923_);
lean_dec(v___y_4922_);
lean_dec_ref(v___y_4921_);
lean_dec_ref(v_ys_4919_);
lean_dec(v___x_4914_);
return v_res_4928_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1(void){
_start:
{
lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; 
v___x_4929_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4930_ = lean_unsigned_to_nat(8u);
v___x_4931_ = lean_unsigned_to_nat(368u);
v___x_4932_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__0));
v___x_4933_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4934_ = l_mkPanicMessageWithDecl(v___x_4933_, v___x_4932_, v___x_4931_, v___x_4930_, v___x_4929_);
return v___x_4934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4935_, lean_object* v_x_4936_, lean_object* v_x_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_){
_start:
{
if (lean_obj_tag(v_x_4936_) == 0)
{
lean_object* v___x_4943_; 
lean_dec_ref(v_xs_4935_);
v___x_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4943_, 0, v_x_4937_);
return v___x_4943_;
}
else
{
lean_object* v_head_4944_; 
v_head_4944_ = lean_ctor_get(v_x_4936_, 0);
if (lean_obj_tag(v_head_4944_) == 0)
{
lean_object* v_tail_4945_; lean_object* v___f_4946_; uint8_t v___x_4947_; 
v_tail_4945_ = lean_ctor_get(v_x_4936_, 1);
lean_inc_n(v_tail_4945_, 2);
lean_dec_ref(v_x_4936_);
v___f_4946_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0));
v___x_4947_ = l_List_all___redArg(v_tail_4945_, v___f_4946_);
if (v___x_4947_ == 0)
{
uint8_t v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___f_4952_; lean_object* v___x_4953_; 
v___x_4948_ = 1;
v___x_4949_ = lean_unsigned_to_nat(1u);
v___x_4950_ = lean_box(v___x_4947_);
v___x_4951_ = lean_box(v___x_4948_);
v___f_4952_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4952_, 0, v___x_4949_);
lean_closure_set(v___f_4952_, 1, v_xs_4935_);
lean_closure_set(v___f_4952_, 2, v_tail_4945_);
lean_closure_set(v___f_4952_, 3, v___x_4950_);
lean_closure_set(v___f_4952_, 4, v___x_4951_);
v___x_4953_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(v_x_4937_, v___x_4949_, v___f_4952_, v___x_4947_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_);
return v___x_4953_;
}
else
{
lean_object* v___x_4954_; 
lean_dec(v_tail_4945_);
lean_dec_ref(v_xs_4935_);
v___x_4954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4954_, 0, v_x_4937_);
return v___x_4954_;
}
}
else
{
lean_object* v_tail_4955_; lean_object* v_val_4956_; lean_object* v___x_4957_; uint8_t v___x_4958_; 
lean_inc_ref(v_head_4944_);
v_tail_4955_ = lean_ctor_get(v_x_4936_, 1);
lean_inc(v_tail_4955_);
lean_dec_ref(v_x_4936_);
v_val_4956_ = lean_ctor_get(v_head_4944_, 0);
lean_inc(v_val_4956_);
lean_dec_ref(v_head_4944_);
v___x_4957_ = lean_array_get_size(v_xs_4935_);
v___x_4958_ = lean_nat_dec_lt(v_val_4956_, v___x_4957_);
if (v___x_4958_ == 0)
{
lean_object* v___x_4959_; lean_object* v___x_4960_; 
lean_dec(v_val_4956_);
lean_dec(v_tail_4955_);
lean_dec_ref(v_x_4937_);
lean_dec_ref(v_xs_4935_);
v___x_4959_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1);
v___x_4960_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4959_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_);
return v___x_4960_;
}
else
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4961_ = l_Lean_instInhabitedExpr;
v___x_4962_ = lean_array_get_borrowed(v___x_4961_, v_xs_4935_, v_val_4956_);
lean_dec(v_val_4956_);
v___x_4963_ = lean_unsigned_to_nat(1u);
v___x_4964_ = lean_mk_empty_array_with_capacity(v___x_4963_);
lean_inc(v___x_4962_);
v___x_4965_ = lean_array_push(v___x_4964_, v___x_4962_);
v___x_4966_ = l_Lean_Meta_instantiateLambda(v_x_4937_, v___x_4965_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_);
lean_dec_ref(v___x_4965_);
if (lean_obj_tag(v___x_4966_) == 0)
{
lean_object* v_a_4967_; 
v_a_4967_ = lean_ctor_get(v___x_4966_, 0);
lean_inc(v_a_4967_);
lean_dec_ref(v___x_4966_);
v_x_4936_ = v_tail_4955_;
v_x_4937_ = v_a_4967_;
goto _start;
}
else
{
lean_dec(v_tail_4955_);
lean_dec_ref(v_xs_4935_);
return v___x_4966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1(lean_object* v___x_4969_, lean_object* v_xs_4970_, lean_object* v_tail_4971_, uint8_t v___x_4972_, uint8_t v___x_4973_, lean_object* v_ys_4974_, lean_object* v_value_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_){
_start:
{
lean_object* v___x_4981_; uint8_t v___x_4982_; 
v___x_4981_ = lean_array_get_size(v_ys_4974_);
v___x_4982_ = lean_nat_dec_eq(v___x_4981_, v___x_4969_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; lean_object* v___x_4984_; 
lean_dec_ref(v_value_4975_);
lean_dec(v_tail_4971_);
lean_dec_ref(v_xs_4970_);
v___x_4983_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2);
v___x_4984_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4983_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
return v___x_4984_;
}
else
{
lean_object* v___x_4985_; 
v___x_4985_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4970_, v_tail_4971_, v_value_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; uint8_t v___x_4987_; lean_object* v___x_4988_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_4986_);
lean_dec_ref(v___x_4985_);
v___x_4987_ = 1;
v___x_4988_ = l_Lean_Meta_mkLambdaFVars(v_ys_4974_, v_a_4986_, v___x_4972_, v___x_4973_, v___x_4972_, v___x_4973_, v___x_4987_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
return v___x_4988_;
}
else
{
return v___x_4985_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_4989_, lean_object* v_x_4990_, lean_object* v_x_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4989_, v_x_4990_, v_x_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
lean_dec(v_a_4995_);
lean_dec_ref(v_a_4994_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
return v_res_4997_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_4999_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_5000_ = lean_unsigned_to_nat(2u);
v___x_5001_ = lean_unsigned_to_nat(362u);
v___x_5002_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_5003_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5004_ = l_mkPanicMessageWithDecl(v___x_5003_, v___x_5002_, v___x_5001_, v___x_5000_, v___x_4999_);
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_5005_, lean_object* v_value_u2080_5006_, lean_object* v_xs_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_){
_start:
{
lean_object* v___x_5013_; lean_object* v___x_5014_; uint8_t v___x_5015_; 
v___x_5013_ = lean_array_get_size(v_xs_5007_);
v___x_5014_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5005_);
v___x_5015_ = lean_nat_dec_eq(v___x_5013_, v___x_5014_);
lean_dec(v___x_5014_);
if (v___x_5015_ == 0)
{
lean_object* v___x_5016_; lean_object* v___x_5017_; 
lean_dec_ref(v_xs_5007_);
lean_dec_ref(v_value_u2080_5006_);
lean_dec_ref(v_perm_5005_);
v___x_5016_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_5017_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5016_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_);
return v___x_5017_;
}
else
{
lean_object* v_mask_5018_; lean_object* v___x_5019_; 
v_mask_5018_ = lean_array_to_list(v_perm_5005_);
v___x_5019_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5007_, v_mask_5018_, v_value_u2080_5006_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_);
return v___x_5019_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_5020_, lean_object* v_value_u2080_5021_, lean_object* v_xs_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_5020_, v_value_u2080_5021_, v_xs_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
lean_dec(v_a_5026_);
lean_dec_ref(v_a_5025_);
lean_dec(v_a_5024_);
lean_dec_ref(v_a_5023_);
return v_res_5028_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_5036_; 
v___x_5036_ = l_Array_instInhabited(lean_box(0));
return v___x_5036_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5037_){
_start:
{
lean_object* v___f_5038_; lean_object* v___f_5039_; lean_object* v___f_5040_; lean_object* v___f_5041_; lean_object* v___f_5042_; lean_object* v___f_5043_; lean_object* v___f_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; 
v___f_5038_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5039_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5040_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5041_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5042_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5043_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5044_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5045_, 0, v___f_5038_);
lean_ctor_set(v___x_5045_, 1, v___f_5039_);
v___x_5046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5046_, 0, v___x_5045_);
lean_ctor_set(v___x_5046_, 1, v___f_5040_);
lean_ctor_set(v___x_5046_, 2, v___f_5041_);
lean_ctor_set(v___x_5046_, 3, v___f_5042_);
lean_ctor_set(v___x_5046_, 4, v___f_5043_);
v___x_5047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5047_, 0, v___x_5046_);
lean_ctor_set(v___x_5047_, 1, v___f_5044_);
v___x_5048_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5049_ = l_instInhabitedOfMonad___redArg(v___x_5047_, v___x_5048_);
v___x_5050_ = lean_panic_fn_borrowed(v___x_5049_, v_msg_5037_);
lean_dec(v___x_5049_);
return v___x_5050_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5051_, lean_object* v_msg_5052_){
_start:
{
lean_object* v___x_5053_; 
v___x_5053_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5052_);
return v___x_5053_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5056_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5057_ = lean_unsigned_to_nat(8u);
v___x_5058_ = lean_unsigned_to_nat(394u);
v___x_5059_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5060_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5061_ = l_mkPanicMessageWithDecl(v___x_5060_, v___x_5059_, v___x_5058_, v___x_5057_, v___x_5056_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5062_, lean_object* v_x_5063_){
_start:
{
if (lean_obj_tag(v_x_5062_) == 0)
{
return v_x_5063_;
}
else
{
lean_object* v_head_5064_; lean_object* v_fst_5065_; 
v_head_5064_ = lean_ctor_get(v_x_5062_, 0);
v_fst_5065_ = lean_ctor_get(v_head_5064_, 0);
if (lean_obj_tag(v_fst_5065_) == 0)
{
lean_object* v_tail_5066_; 
v_tail_5066_ = lean_ctor_get(v_x_5062_, 1);
lean_inc(v_tail_5066_);
lean_dec_ref(v_x_5062_);
v_x_5062_ = v_tail_5066_;
goto _start;
}
else
{
lean_object* v_tail_5068_; lean_object* v_snd_5069_; lean_object* v_val_5070_; lean_object* v___x_5071_; uint8_t v___x_5072_; 
lean_inc_ref(v_fst_5065_);
lean_inc(v_head_5064_);
v_tail_5068_ = lean_ctor_get(v_x_5062_, 1);
lean_inc(v_tail_5068_);
lean_dec_ref(v_x_5062_);
v_snd_5069_ = lean_ctor_get(v_head_5064_, 1);
lean_inc(v_snd_5069_);
lean_dec(v_head_5064_);
v_val_5070_ = lean_ctor_get(v_fst_5065_, 0);
lean_inc(v_val_5070_);
lean_dec_ref(v_fst_5065_);
v___x_5071_ = lean_array_get_size(v_x_5063_);
v___x_5072_ = lean_nat_dec_lt(v_val_5070_, v___x_5071_);
if (v___x_5072_ == 0)
{
lean_object* v___x_5073_; lean_object* v___x_5074_; 
lean_dec(v_val_5070_);
lean_dec(v_snd_5069_);
lean_dec(v_tail_5068_);
lean_dec_ref(v_x_5063_);
v___x_5073_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5074_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5073_);
return v___x_5074_;
}
else
{
lean_object* v___x_5075_; 
v___x_5075_ = lean_array_set(v_x_5063_, v_val_5070_, v_snd_5069_);
lean_dec(v_val_5070_);
v_x_5062_ = v_tail_5068_;
v_x_5063_ = v___x_5075_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5077_, lean_object* v_x_5078_, lean_object* v_x_5079_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5078_, v_x_5079_);
return v___x_5080_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; 
v___x_5083_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5084_ = lean_unsigned_to_nat(2u);
v___x_5085_ = lean_unsigned_to_nat(384u);
v___x_5086_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5087_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5088_ = l_mkPanicMessageWithDecl(v___x_5087_, v___x_5086_, v___x_5085_, v___x_5084_, v___x_5083_);
return v___x_5088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5091_, lean_object* v_xs_5092_){
_start:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; uint8_t v___x_5095_; 
v___x_5093_ = lean_array_get_size(v_xs_5092_);
v___x_5094_ = lean_array_get_size(v_perm_5091_);
v___x_5095_ = lean_nat_dec_eq(v___x_5093_, v___x_5094_);
if (v___x_5095_ == 0)
{
lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5096_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5097_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5096_);
return v___x_5097_;
}
else
{
lean_object* v___x_5098_; uint8_t v___x_5099_; 
v___x_5098_ = lean_unsigned_to_nat(0u);
v___x_5099_ = lean_nat_dec_eq(v___x_5093_, v___x_5098_);
if (v___x_5099_ == 0)
{
lean_object* v_dummy_5100_; lean_object* v___x_5101_; lean_object* v_ys_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; 
v_dummy_5100_ = lean_array_fget_borrowed(v_xs_5092_, v___x_5098_);
v___x_5101_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5091_);
lean_inc(v_dummy_5100_);
v_ys_5102_ = lean_mk_array(v___x_5101_, v_dummy_5100_);
v___x_5103_ = l_Array_zip___redArg(v_perm_5091_, v_xs_5092_);
v___x_5104_ = lean_array_to_list(v___x_5103_);
v___x_5105_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5104_, v_ys_5102_);
return v___x_5105_;
}
else
{
lean_object* v___x_5106_; 
v___x_5106_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5107_, lean_object* v_xs_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5107_, v_xs_5108_);
lean_dec_ref(v_xs_5108_);
lean_dec_ref(v_perm_5107_);
return v_res_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5110_, lean_object* v_perm_5111_, lean_object* v_xs_5112_){
_start:
{
lean_object* v___x_5113_; 
v___x_5113_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5111_, v_xs_5112_);
return v___x_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5114_, lean_object* v_perm_5115_, lean_object* v_xs_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5114_, v_perm_5115_, v_xs_5116_);
lean_dec_ref(v_xs_5116_);
lean_dec_ref(v_perm_5115_);
return v_res_5117_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5118_, lean_object* v_upperBound_5119_, lean_object* v_perm_5120_, lean_object* v_a_5121_, lean_object* v_b_5122_){
_start:
{
lean_object* v_a_5124_; uint8_t v___x_5131_; 
v___x_5131_ = lean_nat_dec_lt(v_a_5121_, v_upperBound_5119_);
if (v___x_5131_ == 0)
{
lean_dec(v_a_5121_);
return v_b_5122_;
}
else
{
lean_object* v___x_5132_; uint8_t v___x_5133_; 
v___x_5132_ = lean_array_get_size(v_perm_5120_);
v___x_5133_ = lean_nat_dec_lt(v_a_5121_, v___x_5132_);
if (v___x_5133_ == 0)
{
goto v___jp_5128_;
}
else
{
lean_object* v___x_5134_; 
v___x_5134_ = lean_array_fget_borrowed(v_perm_5120_, v_a_5121_);
if (lean_obj_tag(v___x_5134_) == 0)
{
goto v___jp_5128_;
}
else
{
v_a_5124_ = v_b_5122_;
goto v___jp_5123_;
}
}
}
v___jp_5123_:
{
lean_object* v___x_5125_; lean_object* v___x_5126_; 
v___x_5125_ = lean_unsigned_to_nat(1u);
v___x_5126_ = lean_nat_add(v_a_5121_, v___x_5125_);
lean_dec(v_a_5121_);
v_a_5121_ = v___x_5126_;
v_b_5122_ = v_a_5124_;
goto _start;
}
v___jp_5128_:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5129_ = lean_array_fget_borrowed(v_xs_5118_, v_a_5121_);
lean_inc(v___x_5129_);
v___x_5130_ = lean_array_push(v_b_5122_, v___x_5129_);
v_a_5124_ = v___x_5130_;
goto v___jp_5123_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5135_, lean_object* v_upperBound_5136_, lean_object* v_perm_5137_, lean_object* v_a_5138_, lean_object* v_b_5139_){
_start:
{
lean_object* v_res_5140_; 
v_res_5140_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5135_, v_upperBound_5136_, v_perm_5137_, v_a_5138_, v_b_5139_);
lean_dec_ref(v_perm_5137_);
lean_dec(v_upperBound_5136_);
lean_dec_ref(v_xs_5135_);
return v_res_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5141_, lean_object* v_xs_5142_){
_start:
{
lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v_ys_5145_; lean_object* v___x_5146_; 
v___x_5143_ = lean_array_get_size(v_xs_5142_);
v___x_5144_ = lean_unsigned_to_nat(0u);
v_ys_5145_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5146_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5142_, v___x_5143_, v_perm_5141_, v___x_5144_, v_ys_5145_);
return v___x_5146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5147_, lean_object* v_xs_5148_){
_start:
{
lean_object* v_res_5149_; 
v_res_5149_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5147_, v_xs_5148_);
lean_dec_ref(v_xs_5148_);
lean_dec_ref(v_perm_5147_);
return v_res_5149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5150_, lean_object* v_perm_5151_, lean_object* v_xs_5152_){
_start:
{
lean_object* v___x_5153_; 
v___x_5153_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5151_, v_xs_5152_);
return v___x_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5154_, lean_object* v_perm_5155_, lean_object* v_xs_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5154_, v_perm_5155_, v_xs_5156_);
lean_dec_ref(v_xs_5156_);
lean_dec_ref(v_perm_5155_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5158_, lean_object* v_xs_5159_, lean_object* v_upperBound_5160_, lean_object* v_perm_5161_, lean_object* v_inst_5162_, lean_object* v_R_5163_, lean_object* v_a_5164_, lean_object* v_b_5165_, lean_object* v_c_5166_){
_start:
{
lean_object* v___x_5167_; 
v___x_5167_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5159_, v_upperBound_5160_, v_perm_5161_, v_a_5164_, v_b_5165_);
return v___x_5167_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5168_, lean_object* v_xs_5169_, lean_object* v_upperBound_5170_, lean_object* v_perm_5171_, lean_object* v_inst_5172_, lean_object* v_R_5173_, lean_object* v_a_5174_, lean_object* v_b_5175_, lean_object* v_c_5176_){
_start:
{
lean_object* v_res_5177_; 
v_res_5177_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5168_, v_xs_5169_, v_upperBound_5170_, v_perm_5171_, v_inst_5172_, v_R_5173_, v_a_5174_, v_b_5175_, v_c_5176_);
lean_dec_ref(v_perm_5171_);
lean_dec(v_upperBound_5170_);
lean_dec_ref(v_xs_5169_);
return v_res_5177_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(lean_object* v_msg_5178_){
_start:
{
lean_object* v___x_5179_; lean_object* v___x_5180_; 
v___x_5179_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5180_ = lean_panic_fn_borrowed(v___x_5179_, v_msg_5178_);
return v___x_5180_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_00_u03b1_5181_, lean_object* v_msg_5182_){
_start:
{
lean_object* v___x_5183_; 
v___x_5183_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v_msg_5182_);
return v___x_5183_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_as_5184_, size_t v_i_5185_, size_t v_stop_5186_){
_start:
{
uint8_t v___x_5187_; 
v___x_5187_ = lean_usize_dec_eq(v_i_5185_, v_stop_5186_);
if (v___x_5187_ == 0)
{
uint8_t v___x_5188_; lean_object* v___x_5189_; 
v___x_5188_ = 1;
v___x_5189_ = lean_array_uget_borrowed(v_as_5184_, v_i_5185_);
if (lean_obj_tag(v___x_5189_) == 0)
{
if (v___x_5187_ == 0)
{
size_t v___x_5190_; size_t v___x_5191_; 
v___x_5190_ = ((size_t)1ULL);
v___x_5191_ = lean_usize_add(v_i_5185_, v___x_5190_);
v_i_5185_ = v___x_5191_;
goto _start;
}
else
{
return v___x_5188_;
}
}
else
{
return v___x_5188_;
}
}
else
{
uint8_t v___x_5193_; 
v___x_5193_ = 0;
return v___x_5193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___boxed(lean_object* v_as_5194_, lean_object* v_i_5195_, lean_object* v_stop_5196_){
_start:
{
size_t v_i_boxed_5197_; size_t v_stop_boxed_5198_; uint8_t v_res_5199_; lean_object* v_r_5200_; 
v_i_boxed_5197_ = lean_unbox_usize(v_i_5195_);
lean_dec(v_i_5195_);
v_stop_boxed_5198_ = lean_unbox_usize(v_stop_5196_);
lean_dec(v_stop_5196_);
v_res_5199_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v_as_5194_, v_i_boxed_5197_, v_stop_boxed_5198_);
lean_dec_ref(v_as_5194_);
v_r_5200_ = lean_box(v_res_5199_);
return v_r_5200_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
v___x_5203_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5204_ = lean_unsigned_to_nat(12u);
v___x_5205_ = lean_unsigned_to_nat(433u);
v___x_5206_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5207_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5208_ = l_mkPanicMessageWithDecl(v___x_5207_, v___x_5206_, v___x_5205_, v___x_5204_, v___x_5203_);
return v___x_5208_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; 
v___x_5210_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5211_ = lean_unsigned_to_nat(10u);
v___x_5212_ = lean_unsigned_to_nat(425u);
v___x_5213_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5214_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5215_ = l_mkPanicMessageWithDecl(v___x_5214_, v___x_5213_, v___x_5212_, v___x_5211_, v___x_5210_);
return v___x_5215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5216_, lean_object* v_fixedArgs_5217_, lean_object* v_varyingArgs_5218_, lean_object* v_i_5219_, lean_object* v_j_5220_, lean_object* v_xs_5221_){
_start:
{
lean_object* v_lower_5223_; lean_object* v_upper_5224_; lean_object* v___y_5229_; lean_object* v___y_5230_; lean_object* v___y_5231_; lean_object* v_lower_5239_; lean_object* v_upper_5240_; lean_object* v___x_5248_; uint8_t v___x_5249_; 
v___x_5248_ = lean_array_get_size(v_perm_5216_);
v___x_5249_ = lean_nat_dec_lt(v_i_5219_, v___x_5248_);
if (v___x_5249_ == 0)
{
lean_object* v___x_5250_; lean_object* v___x_5251_; uint8_t v___x_5252_; 
lean_dec(v_i_5219_);
lean_dec_ref(v_perm_5216_);
v___x_5250_ = lean_unsigned_to_nat(0u);
v___x_5251_ = lean_array_get_size(v_varyingArgs_5218_);
v___x_5252_ = lean_nat_dec_le(v_j_5220_, v___x_5250_);
if (v___x_5252_ == 0)
{
v_lower_5223_ = v_j_5220_;
v_upper_5224_ = v___x_5251_;
goto v___jp_5222_;
}
else
{
lean_dec(v_j_5220_);
v_lower_5223_ = v___x_5250_;
v_upper_5224_ = v___x_5251_;
goto v___jp_5222_;
}
}
else
{
lean_object* v___x_5253_; 
v___x_5253_ = lean_array_fget_borrowed(v_perm_5216_, v_i_5219_);
if (lean_obj_tag(v___x_5253_) == 1)
{
lean_object* v_val_5254_; lean_object* v___x_5255_; uint8_t v___x_5256_; 
v_val_5254_ = lean_ctor_get(v___x_5253_, 0);
v___x_5255_ = lean_array_get_size(v_fixedArgs_5217_);
v___x_5256_ = lean_nat_dec_lt(v_val_5254_, v___x_5255_);
if (v___x_5256_ == 0)
{
lean_object* v___x_5257_; lean_object* v___x_5258_; 
lean_dec_ref(v_xs_5221_);
lean_dec(v_j_5220_);
lean_dec(v_i_5219_);
lean_dec_ref(v_varyingArgs_5218_);
lean_dec_ref(v_perm_5216_);
v___x_5257_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5258_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5257_);
return v___x_5258_;
}
else
{
lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5259_ = lean_unsigned_to_nat(1u);
v___x_5260_ = lean_nat_add(v_i_5219_, v___x_5259_);
lean_dec(v_i_5219_);
v___x_5261_ = lean_array_fget_borrowed(v_fixedArgs_5217_, v_val_5254_);
lean_inc(v___x_5261_);
v___x_5262_ = lean_array_push(v_xs_5221_, v___x_5261_);
v_i_5219_ = v___x_5260_;
v_xs_5221_ = v___x_5262_;
goto _start;
}
}
else
{
lean_object* v___x_5264_; uint8_t v___x_5265_; 
v___x_5264_ = lean_array_get_size(v_varyingArgs_5218_);
v___x_5265_ = lean_nat_dec_lt(v_j_5220_, v___x_5264_);
if (v___x_5265_ == 0)
{
lean_object* v___x_5266_; uint8_t v___x_5267_; 
lean_dec(v_j_5220_);
lean_dec_ref(v_varyingArgs_5218_);
v___x_5266_ = lean_unsigned_to_nat(0u);
v___x_5267_ = lean_nat_dec_le(v_i_5219_, v___x_5266_);
if (v___x_5267_ == 0)
{
v_lower_5239_ = v_i_5219_;
v_upper_5240_ = v___x_5248_;
goto v___jp_5238_;
}
else
{
lean_dec(v_i_5219_);
v_lower_5239_ = v___x_5266_;
v_upper_5240_ = v___x_5248_;
goto v___jp_5238_;
}
}
else
{
lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; 
v___x_5268_ = lean_unsigned_to_nat(1u);
v___x_5269_ = lean_nat_add(v_i_5219_, v___x_5268_);
lean_dec(v_i_5219_);
v___x_5270_ = lean_nat_add(v_j_5220_, v___x_5268_);
v___x_5271_ = lean_array_fget_borrowed(v_varyingArgs_5218_, v_j_5220_);
lean_dec(v_j_5220_);
lean_inc(v___x_5271_);
v___x_5272_ = lean_array_push(v_xs_5221_, v___x_5271_);
v_i_5219_ = v___x_5269_;
v_j_5220_ = v___x_5270_;
v_xs_5221_ = v___x_5272_;
goto _start;
}
}
}
v___jp_5222_:
{
lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; 
v___x_5225_ = l_Array_toSubarray___redArg(v_varyingArgs_5218_, v_lower_5223_, v_upper_5224_);
v___x_5226_ = l_Subarray_copy___redArg(v___x_5225_);
v___x_5227_ = l_Array_append___redArg(v_xs_5221_, v___x_5226_);
lean_dec_ref(v___x_5226_);
return v___x_5227_;
}
v___jp_5228_:
{
uint8_t v___x_5232_; 
v___x_5232_ = lean_nat_dec_lt(v___y_5229_, v___y_5231_);
if (v___x_5232_ == 0)
{
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
lean_dec(v___y_5229_);
return v_xs_5221_;
}
else
{
size_t v___x_5233_; size_t v___x_5234_; uint8_t v___x_5235_; 
v___x_5233_ = lean_usize_of_nat(v___y_5229_);
lean_dec(v___y_5229_);
v___x_5234_ = lean_usize_of_nat(v___y_5231_);
lean_dec(v___y_5231_);
v___x_5235_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v___y_5230_, v___x_5233_, v___x_5234_);
lean_dec_ref(v___y_5230_);
if (v___x_5235_ == 0)
{
return v_xs_5221_;
}
else
{
lean_object* v___x_5236_; lean_object* v___x_5237_; 
lean_dec_ref(v_xs_5221_);
v___x_5236_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5237_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5236_);
return v___x_5237_;
}
}
}
v___jp_5238_:
{
lean_object* v___x_5241_; lean_object* v_array_5242_; lean_object* v_start_5243_; lean_object* v_stop_5244_; uint8_t v___x_5245_; 
v___x_5241_ = l_Array_toSubarray___redArg(v_perm_5216_, v_lower_5239_, v_upper_5240_);
v_array_5242_ = lean_ctor_get(v___x_5241_, 0);
lean_inc_ref(v_array_5242_);
v_start_5243_ = lean_ctor_get(v___x_5241_, 1);
lean_inc(v_start_5243_);
v_stop_5244_ = lean_ctor_get(v___x_5241_, 2);
lean_inc(v_stop_5244_);
lean_dec_ref(v___x_5241_);
v___x_5245_ = lean_nat_dec_lt(v_start_5243_, v_stop_5244_);
if (v___x_5245_ == 0)
{
lean_dec(v_stop_5244_);
lean_dec(v_start_5243_);
lean_dec_ref(v_array_5242_);
return v_xs_5221_;
}
else
{
lean_object* v___x_5246_; uint8_t v___x_5247_; 
v___x_5246_ = lean_array_get_size(v_array_5242_);
v___x_5247_ = lean_nat_dec_le(v_stop_5244_, v___x_5246_);
if (v___x_5247_ == 0)
{
lean_dec(v_stop_5244_);
v___y_5229_ = v_start_5243_;
v___y_5230_ = v_array_5242_;
v___y_5231_ = v___x_5246_;
goto v___jp_5228_;
}
else
{
v___y_5229_ = v_start_5243_;
v___y_5230_ = v_array_5242_;
v___y_5231_ = v_stop_5244_;
goto v___jp_5228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5274_, lean_object* v_fixedArgs_5275_, lean_object* v_varyingArgs_5276_, lean_object* v_i_5277_, lean_object* v_j_5278_, lean_object* v_xs_5279_){
_start:
{
lean_object* v_res_5280_; 
v_res_5280_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5274_, v_fixedArgs_5275_, v_varyingArgs_5276_, v_i_5277_, v_j_5278_, v_xs_5279_);
lean_dec_ref(v_fixedArgs_5275_);
return v_res_5280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5281_, lean_object* v_perm_5282_, lean_object* v_fixedArgs_5283_, lean_object* v_varyingArgs_5284_, lean_object* v_i_5285_, lean_object* v_j_5286_, lean_object* v_xs_5287_){
_start:
{
lean_object* v___x_5288_; 
v___x_5288_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5282_, v_fixedArgs_5283_, v_varyingArgs_5284_, v_i_5285_, v_j_5286_, v_xs_5287_);
return v___x_5288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5289_, lean_object* v_perm_5290_, lean_object* v_fixedArgs_5291_, lean_object* v_varyingArgs_5292_, lean_object* v_i_5293_, lean_object* v_j_5294_, lean_object* v_xs_5295_){
_start:
{
lean_object* v_res_5296_; 
v_res_5296_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5289_, v_perm_5290_, v_fixedArgs_5291_, v_varyingArgs_5292_, v_i_5293_, v_j_5294_, v_xs_5295_);
lean_dec_ref(v_fixedArgs_5291_);
return v_res_5296_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5299_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5300_ = lean_unsigned_to_nat(2u);
v___x_5301_ = lean_unsigned_to_nat(416u);
v___x_5302_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5303_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5304_ = l_mkPanicMessageWithDecl(v___x_5303_, v___x_5302_, v___x_5301_, v___x_5300_, v___x_5299_);
return v___x_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5305_, lean_object* v_fixedArgs_5306_, lean_object* v_varyingArgs_5307_){
_start:
{
lean_object* v___x_5308_; lean_object* v___x_5309_; uint8_t v___x_5310_; 
v___x_5308_ = lean_array_get_size(v_fixedArgs_5306_);
v___x_5309_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5305_);
v___x_5310_ = lean_nat_dec_eq(v___x_5308_, v___x_5309_);
lean_dec(v___x_5309_);
if (v___x_5310_ == 0)
{
lean_object* v___x_5311_; lean_object* v___x_5312_; 
lean_dec_ref(v_varyingArgs_5307_);
lean_dec_ref(v_perm_5305_);
v___x_5311_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5312_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5311_);
return v___x_5312_;
}
else
{
lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; 
v___x_5313_ = lean_unsigned_to_nat(0u);
v___x_5314_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5315_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5305_, v_fixedArgs_5306_, v_varyingArgs_5307_, v___x_5313_, v___x_5313_, v___x_5314_);
return v___x_5315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5316_, lean_object* v_fixedArgs_5317_, lean_object* v_varyingArgs_5318_){
_start:
{
lean_object* v_res_5319_; 
v_res_5319_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5316_, v_fixedArgs_5317_, v_varyingArgs_5318_);
lean_dec_ref(v_fixedArgs_5317_);
return v_res_5319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5320_, lean_object* v_perm_5321_, lean_object* v_fixedArgs_5322_, lean_object* v_varyingArgs_5323_){
_start:
{
lean_object* v___x_5324_; 
v___x_5324_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5321_, v_fixedArgs_5322_, v_varyingArgs_5323_);
return v___x_5324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5325_, lean_object* v_perm_5326_, lean_object* v_fixedArgs_5327_, lean_object* v_varyingArgs_5328_){
_start:
{
lean_object* v_res_5329_; 
v_res_5329_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5325_, v_perm_5326_, v_fixedArgs_5327_, v_varyingArgs_5328_);
lean_dec_ref(v_fixedArgs_5327_);
return v_res_5329_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5330_, lean_object* v_x_5331_){
_start:
{
if (lean_obj_tag(v_x_5330_) == 0)
{
if (lean_obj_tag(v_x_5331_) == 0)
{
uint8_t v___x_5332_; 
v___x_5332_ = 1;
return v___x_5332_;
}
else
{
uint8_t v___x_5333_; 
v___x_5333_ = 0;
return v___x_5333_;
}
}
else
{
if (lean_obj_tag(v_x_5331_) == 0)
{
uint8_t v___x_5334_; 
v___x_5334_ = 0;
return v___x_5334_;
}
else
{
lean_object* v_val_5335_; lean_object* v_val_5336_; uint8_t v___x_5337_; 
v_val_5335_ = lean_ctor_get(v_x_5330_, 0);
v_val_5336_ = lean_ctor_get(v_x_5331_, 0);
v___x_5337_ = lean_nat_dec_eq(v_val_5335_, v_val_5336_);
return v___x_5337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5338_, lean_object* v_x_5339_){
_start:
{
uint8_t v_res_5340_; lean_object* v_r_5341_; 
v_res_5340_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5338_, v_x_5339_);
lean_dec(v_x_5339_);
lean_dec(v_x_5338_);
v_r_5341_ = lean_box(v_res_5340_);
return v_r_5341_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5342_, lean_object* v_ys_5343_, lean_object* v_x_5344_){
_start:
{
lean_object* v_zero_5345_; uint8_t v_isZero_5346_; 
v_zero_5345_ = lean_unsigned_to_nat(0u);
v_isZero_5346_ = lean_nat_dec_eq(v_x_5344_, v_zero_5345_);
if (v_isZero_5346_ == 1)
{
lean_dec(v_x_5344_);
return v_isZero_5346_;
}
else
{
lean_object* v_one_5347_; lean_object* v_n_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; uint8_t v___x_5351_; 
v_one_5347_ = lean_unsigned_to_nat(1u);
v_n_5348_ = lean_nat_sub(v_x_5344_, v_one_5347_);
lean_dec(v_x_5344_);
v___x_5349_ = lean_array_fget_borrowed(v_xs_5342_, v_n_5348_);
v___x_5350_ = lean_array_fget_borrowed(v_ys_5343_, v_n_5348_);
v___x_5351_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5349_, v___x_5350_);
if (v___x_5351_ == 0)
{
lean_dec(v_n_5348_);
return v___x_5351_;
}
else
{
v_x_5344_ = v_n_5348_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5353_, lean_object* v_ys_5354_, lean_object* v_x_5355_){
_start:
{
uint8_t v_res_5356_; lean_object* v_r_5357_; 
v_res_5356_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5353_, v_ys_5354_, v_x_5355_);
lean_dec_ref(v_ys_5354_);
lean_dec_ref(v_xs_5353_);
v_r_5357_ = lean_box(v_res_5356_);
return v_r_5357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5358_, size_t v_i_5359_, lean_object* v_bs_5360_){
_start:
{
uint8_t v___x_5361_; 
v___x_5361_ = lean_usize_dec_lt(v_i_5359_, v_sz_5358_);
if (v___x_5361_ == 0)
{
return v_bs_5360_;
}
else
{
lean_object* v_v_5362_; lean_object* v___x_5363_; lean_object* v_bs_x27_5364_; lean_object* v___x_5365_; size_t v___x_5366_; size_t v___x_5367_; lean_object* v___x_5368_; 
v_v_5362_ = lean_array_uget(v_bs_5360_, v_i_5359_);
v___x_5363_ = lean_unsigned_to_nat(0u);
v_bs_x27_5364_ = lean_array_uset(v_bs_5360_, v_i_5359_, v___x_5363_);
v___x_5365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5365_, 0, v_v_5362_);
v___x_5366_ = ((size_t)1ULL);
v___x_5367_ = lean_usize_add(v_i_5359_, v___x_5366_);
v___x_5368_ = lean_array_uset(v_bs_x27_5364_, v_i_5359_, v___x_5365_);
v_i_5359_ = v___x_5367_;
v_bs_5360_ = v___x_5368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5370_, lean_object* v_i_5371_, lean_object* v_bs_5372_){
_start:
{
size_t v_sz_boxed_5373_; size_t v_i_boxed_5374_; lean_object* v_res_5375_; 
v_sz_boxed_5373_ = lean_unbox_usize(v_sz_5370_);
lean_dec(v_sz_5370_);
v_i_boxed_5374_ = lean_unbox_usize(v_i_5371_);
lean_dec(v_i_5371_);
v_res_5375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5373_, v_i_boxed_5374_, v_bs_5372_);
return v_res_5375_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5376_, lean_object* v_as_5377_, size_t v_i_5378_, size_t v_stop_5379_){
_start:
{
uint8_t v___x_5380_; 
v___x_5380_ = lean_usize_dec_eq(v_i_5378_, v_stop_5379_);
if (v___x_5380_ == 0)
{
lean_object* v_numFixed_5381_; uint8_t v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; size_t v_sz_5385_; size_t v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; uint8_t v___x_5394_; 
v_numFixed_5381_ = lean_ctor_get(v_fixedParamPerms_5376_, 0);
v___x_5382_ = 1;
v___x_5383_ = lean_array_uget_borrowed(v_as_5377_, v_i_5378_);
lean_inc(v_numFixed_5381_);
v___x_5384_ = l_Array_range(v_numFixed_5381_);
v_sz_5385_ = lean_array_size(v___x_5384_);
v___x_5386_ = ((size_t)0ULL);
v___x_5387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5385_, v___x_5386_, v___x_5384_);
v___x_5388_ = lean_array_get_size(v___x_5383_);
v___x_5389_ = lean_nat_sub(v___x_5388_, v_numFixed_5381_);
v___x_5390_ = lean_box(0);
v___x_5391_ = lean_mk_array(v___x_5389_, v___x_5390_);
v___x_5392_ = l_Array_append___redArg(v___x_5387_, v___x_5391_);
lean_dec_ref(v___x_5391_);
v___x_5393_ = lean_array_get_size(v___x_5392_);
v___x_5394_ = lean_nat_dec_eq(v___x_5388_, v___x_5393_);
if (v___x_5394_ == 0)
{
lean_dec_ref(v___x_5392_);
lean_dec_ref(v_fixedParamPerms_5376_);
return v___x_5382_;
}
else
{
uint8_t v___x_5395_; 
v___x_5395_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5383_, v___x_5392_, v___x_5388_);
lean_dec_ref(v___x_5392_);
if (v___x_5395_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5376_);
return v___x_5382_;
}
else
{
if (v___x_5380_ == 0)
{
size_t v___x_5396_; size_t v___x_5397_; 
v___x_5396_ = ((size_t)1ULL);
v___x_5397_ = lean_usize_add(v_i_5378_, v___x_5396_);
v_i_5378_ = v___x_5397_;
goto _start;
}
else
{
lean_dec_ref(v_fixedParamPerms_5376_);
return v___x_5382_;
}
}
}
}
else
{
uint8_t v___x_5399_; 
lean_dec_ref(v_fixedParamPerms_5376_);
v___x_5399_ = 0;
return v___x_5399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5400_, lean_object* v_as_5401_, lean_object* v_i_5402_, lean_object* v_stop_5403_){
_start:
{
size_t v_i_boxed_5404_; size_t v_stop_boxed_5405_; uint8_t v_res_5406_; lean_object* v_r_5407_; 
v_i_boxed_5404_ = lean_unbox_usize(v_i_5402_);
lean_dec(v_i_5402_);
v_stop_boxed_5405_ = lean_unbox_usize(v_stop_5403_);
lean_dec(v_stop_5403_);
v_res_5406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5400_, v_as_5401_, v_i_boxed_5404_, v_stop_boxed_5405_);
lean_dec_ref(v_as_5401_);
v_r_5407_ = lean_box(v_res_5406_);
return v_r_5407_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5408_){
_start:
{
lean_object* v_perms_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; uint8_t v___x_5412_; 
v_perms_5409_ = lean_ctor_get(v_fixedParamPerms_5408_, 1);
lean_inc_ref(v_perms_5409_);
v___x_5410_ = lean_unsigned_to_nat(0u);
v___x_5411_ = lean_array_get_size(v_perms_5409_);
v___x_5412_ = lean_nat_dec_lt(v___x_5410_, v___x_5411_);
if (v___x_5412_ == 0)
{
uint8_t v___x_5413_; 
lean_dec_ref(v_perms_5409_);
lean_dec_ref(v_fixedParamPerms_5408_);
v___x_5413_ = 1;
return v___x_5413_;
}
else
{
if (v___x_5412_ == 0)
{
lean_dec_ref(v_perms_5409_);
lean_dec_ref(v_fixedParamPerms_5408_);
return v___x_5412_;
}
else
{
size_t v___x_5414_; size_t v___x_5415_; uint8_t v___x_5416_; 
v___x_5414_ = ((size_t)0ULL);
v___x_5415_ = lean_usize_of_nat(v___x_5411_);
v___x_5416_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5408_, v_perms_5409_, v___x_5414_, v___x_5415_);
lean_dec_ref(v_perms_5409_);
if (v___x_5416_ == 0)
{
return v___x_5412_;
}
else
{
uint8_t v___x_5417_; 
v___x_5417_ = 0;
return v___x_5417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5418_){
_start:
{
uint8_t v_res_5419_; lean_object* v_r_5420_; 
v_res_5419_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5418_);
v_r_5420_ = lean_box(v_res_5419_);
return v_r_5420_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5421_, lean_object* v_ys_5422_, lean_object* v_hsz_5423_, lean_object* v_x_5424_, lean_object* v_x_5425_){
_start:
{
uint8_t v___x_5426_; 
v___x_5426_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5421_, v_ys_5422_, v_x_5424_);
return v___x_5426_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5427_, lean_object* v_ys_5428_, lean_object* v_hsz_5429_, lean_object* v_x_5430_, lean_object* v_x_5431_){
_start:
{
uint8_t v_res_5432_; lean_object* v_r_5433_; 
v_res_5432_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5427_, v_ys_5428_, v_hsz_5429_, v_x_5430_, v_x_5431_);
lean_dec_ref(v_ys_5428_);
lean_dec_ref(v_xs_5427_);
v_r_5433_ = lean_box(v_res_5432_);
return v_r_5433_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5434_; 
v___x_5434_ = l_Array_instInhabited(lean_box(0));
return v___x_5434_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5435_){
_start:
{
lean_object* v___f_5436_; lean_object* v___f_5437_; lean_object* v___f_5438_; lean_object* v___f_5439_; lean_object* v___f_5440_; lean_object* v___f_5441_; lean_object* v___f_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; 
v___f_5436_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5437_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5438_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5439_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5440_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5441_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5442_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5443_, 0, v___f_5436_);
lean_ctor_set(v___x_5443_, 1, v___f_5437_);
v___x_5444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5444_, 0, v___x_5443_);
lean_ctor_set(v___x_5444_, 1, v___f_5438_);
lean_ctor_set(v___x_5444_, 2, v___f_5439_);
lean_ctor_set(v___x_5444_, 3, v___f_5440_);
lean_ctor_set(v___x_5444_, 4, v___f_5441_);
v___x_5445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5445_, 0, v___x_5444_);
lean_ctor_set(v___x_5445_, 1, v___f_5442_);
v___x_5446_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5447_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5448_, 0, v___x_5447_);
lean_ctor_set(v___x_5448_, 1, v___x_5447_);
v___x_5449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5449_, 0, v___x_5446_);
lean_ctor_set(v___x_5449_, 1, v___x_5448_);
v___x_5450_ = l_instInhabitedOfMonad___redArg(v___x_5445_, v___x_5449_);
v___x_5451_ = lean_panic_fn_borrowed(v___x_5450_, v_msg_5435_);
lean_dec(v___x_5450_);
return v___x_5451_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5452_; 
v___x_5452_ = l_Array_instInhabited(lean_box(0));
return v___x_5452_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5453_){
_start:
{
lean_object* v___f_5454_; lean_object* v___f_5455_; lean_object* v___f_5456_; lean_object* v___f_5457_; lean_object* v___f_5458_; lean_object* v___f_5459_; lean_object* v___f_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; 
v___f_5454_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5455_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5456_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5457_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5458_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5459_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5460_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5461_, 0, v___f_5454_);
lean_ctor_set(v___x_5461_, 1, v___f_5455_);
v___x_5462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5462_, 0, v___x_5461_);
lean_ctor_set(v___x_5462_, 1, v___f_5456_);
lean_ctor_set(v___x_5462_, 2, v___f_5457_);
lean_ctor_set(v___x_5462_, 3, v___f_5458_);
lean_ctor_set(v___x_5462_, 4, v___f_5459_);
v___x_5463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5463_, 0, v___x_5462_);
lean_ctor_set(v___x_5463_, 1, v___f_5460_);
v___x_5464_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5465_, 0, v___x_5464_);
v___x_5466_ = l_instInhabitedOfMonad___redArg(v___x_5463_, v___x_5465_);
v___x_5467_ = lean_panic_fn_borrowed(v___x_5466_, v_msg_5453_);
lean_dec(v___x_5466_);
return v___x_5467_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5468_, lean_object* v_a_5469_, lean_object* v_b_5470_){
_start:
{
lean_object* v_a_5472_; uint8_t v___x_5476_; 
v___x_5476_ = lean_nat_dec_lt(v_a_5469_, v_upperBound_5468_);
if (v___x_5476_ == 0)
{
lean_dec(v_a_5469_);
return v_b_5470_;
}
else
{
lean_object* v_snd_5477_; lean_object* v_snd_5478_; lean_object* v_snd_5479_; lean_object* v_snd_5480_; lean_object* v_fst_5481_; lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5593_; 
v_snd_5477_ = lean_ctor_get(v_b_5470_, 1);
lean_inc(v_snd_5477_);
v_snd_5478_ = lean_ctor_get(v_snd_5477_, 1);
lean_inc(v_snd_5478_);
v_snd_5479_ = lean_ctor_get(v_snd_5478_, 1);
lean_inc(v_snd_5479_);
v_snd_5480_ = lean_ctor_get(v_snd_5479_, 1);
lean_inc(v_snd_5480_);
v_fst_5481_ = lean_ctor_get(v_b_5470_, 0);
v_isSharedCheck_5593_ = !lean_is_exclusive(v_b_5470_);
if (v_isSharedCheck_5593_ == 0)
{
lean_object* v_unused_5594_; 
v_unused_5594_ = lean_ctor_get(v_b_5470_, 1);
lean_dec(v_unused_5594_);
v___x_5483_ = v_b_5470_;
v_isShared_5484_ = v_isSharedCheck_5593_;
goto v_resetjp_5482_;
}
else
{
lean_inc(v_fst_5481_);
lean_dec(v_b_5470_);
v___x_5483_ = lean_box(0);
v_isShared_5484_ = v_isSharedCheck_5593_;
goto v_resetjp_5482_;
}
v_resetjp_5482_:
{
lean_object* v_fst_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5591_; 
v_fst_5485_ = lean_ctor_get(v_snd_5477_, 0);
v_isSharedCheck_5591_ = !lean_is_exclusive(v_snd_5477_);
if (v_isSharedCheck_5591_ == 0)
{
lean_object* v_unused_5592_; 
v_unused_5592_ = lean_ctor_get(v_snd_5477_, 1);
lean_dec(v_unused_5592_);
v___x_5487_ = v_snd_5477_;
v_isShared_5488_ = v_isSharedCheck_5591_;
goto v_resetjp_5486_;
}
else
{
lean_inc(v_fst_5485_);
lean_dec(v_snd_5477_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5591_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v_fst_5489_; lean_object* v___x_5491_; uint8_t v_isShared_5492_; uint8_t v_isSharedCheck_5589_; 
v_fst_5489_ = lean_ctor_get(v_snd_5478_, 0);
v_isSharedCheck_5589_ = !lean_is_exclusive(v_snd_5478_);
if (v_isSharedCheck_5589_ == 0)
{
lean_object* v_unused_5590_; 
v_unused_5590_ = lean_ctor_get(v_snd_5478_, 1);
lean_dec(v_unused_5590_);
v___x_5491_ = v_snd_5478_;
v_isShared_5492_ = v_isSharedCheck_5589_;
goto v_resetjp_5490_;
}
else
{
lean_inc(v_fst_5489_);
lean_dec(v_snd_5478_);
v___x_5491_ = lean_box(0);
v_isShared_5492_ = v_isSharedCheck_5589_;
goto v_resetjp_5490_;
}
v_resetjp_5490_:
{
lean_object* v_fst_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5587_; 
v_fst_5493_ = lean_ctor_get(v_snd_5479_, 0);
v_isSharedCheck_5587_ = !lean_is_exclusive(v_snd_5479_);
if (v_isSharedCheck_5587_ == 0)
{
lean_object* v_unused_5588_; 
v_unused_5588_ = lean_ctor_get(v_snd_5479_, 1);
lean_dec(v_unused_5588_);
v___x_5495_ = v_snd_5479_;
v_isShared_5496_ = v_isSharedCheck_5587_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_fst_5493_);
lean_dec(v_snd_5479_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5587_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v_array_5497_; lean_object* v_start_5498_; lean_object* v_stop_5499_; uint8_t v___x_5500_; 
v_array_5497_ = lean_ctor_get(v_snd_5480_, 0);
v_start_5498_ = lean_ctor_get(v_snd_5480_, 1);
v_stop_5499_ = lean_ctor_get(v_snd_5480_, 2);
v___x_5500_ = lean_nat_dec_lt(v_start_5498_, v_stop_5499_);
if (v___x_5500_ == 0)
{
lean_object* v___x_5502_; 
lean_dec(v_a_5469_);
if (v_isShared_5496_ == 0)
{
v___x_5502_ = v___x_5495_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_fst_5493_);
lean_ctor_set(v_reuseFailAlloc_5512_, 1, v_snd_5480_);
v___x_5502_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
lean_object* v___x_5504_; 
if (v_isShared_5492_ == 0)
{
lean_ctor_set(v___x_5491_, 1, v___x_5502_);
v___x_5504_ = v___x_5491_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v_fst_5489_);
lean_ctor_set(v_reuseFailAlloc_5511_, 1, v___x_5502_);
v___x_5504_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
lean_object* v___x_5506_; 
if (v_isShared_5488_ == 0)
{
lean_ctor_set(v___x_5487_, 1, v___x_5504_);
v___x_5506_ = v___x_5487_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_fst_5485_);
lean_ctor_set(v_reuseFailAlloc_5510_, 1, v___x_5504_);
v___x_5506_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
lean_object* v___x_5508_; 
if (v_isShared_5484_ == 0)
{
lean_ctor_set(v___x_5483_, 1, v___x_5506_);
v___x_5508_ = v___x_5483_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_fst_5481_);
lean_ctor_set(v_reuseFailAlloc_5509_, 1, v___x_5506_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
return v___x_5508_;
}
}
}
}
}
else
{
lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5583_; 
lean_inc(v_stop_5499_);
lean_inc(v_start_5498_);
lean_inc_ref(v_array_5497_);
v_isSharedCheck_5583_ = !lean_is_exclusive(v_snd_5480_);
if (v_isSharedCheck_5583_ == 0)
{
lean_object* v_unused_5584_; lean_object* v_unused_5585_; lean_object* v_unused_5586_; 
v_unused_5584_ = lean_ctor_get(v_snd_5480_, 2);
lean_dec(v_unused_5584_);
v_unused_5585_ = lean_ctor_get(v_snd_5480_, 1);
lean_dec(v_unused_5585_);
v_unused_5586_ = lean_ctor_get(v_snd_5480_, 0);
lean_dec(v_unused_5586_);
v___x_5514_ = v_snd_5480_;
v_isShared_5515_ = v_isSharedCheck_5583_;
goto v_resetjp_5513_;
}
else
{
lean_dec(v_snd_5480_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5583_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v_array_5516_; lean_object* v_start_5517_; lean_object* v_stop_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5523_; 
v_array_5516_ = lean_ctor_get(v_fst_5493_, 0);
v_start_5517_ = lean_ctor_get(v_fst_5493_, 1);
v_stop_5518_ = lean_ctor_get(v_fst_5493_, 2);
v___x_5519_ = lean_array_fget(v_array_5497_, v_start_5498_);
v___x_5520_ = lean_unsigned_to_nat(1u);
v___x_5521_ = lean_nat_add(v_start_5498_, v___x_5520_);
lean_dec(v_start_5498_);
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 1, v___x_5521_);
v___x_5523_ = v___x_5514_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v_array_5497_);
lean_ctor_set(v_reuseFailAlloc_5582_, 1, v___x_5521_);
lean_ctor_set(v_reuseFailAlloc_5582_, 2, v_stop_5499_);
v___x_5523_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
uint8_t v___x_5524_; 
v___x_5524_ = lean_nat_dec_lt(v_start_5517_, v_stop_5518_);
if (v___x_5524_ == 0)
{
lean_object* v___x_5526_; 
lean_dec(v___x_5519_);
lean_dec(v_a_5469_);
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 1, v___x_5523_);
v___x_5526_ = v___x_5495_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5536_; 
v_reuseFailAlloc_5536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_fst_5493_);
lean_ctor_set(v_reuseFailAlloc_5536_, 1, v___x_5523_);
v___x_5526_ = v_reuseFailAlloc_5536_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
lean_object* v___x_5528_; 
if (v_isShared_5492_ == 0)
{
lean_ctor_set(v___x_5491_, 1, v___x_5526_);
v___x_5528_ = v___x_5491_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5535_; 
v_reuseFailAlloc_5535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_fst_5489_);
lean_ctor_set(v_reuseFailAlloc_5535_, 1, v___x_5526_);
v___x_5528_ = v_reuseFailAlloc_5535_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
lean_object* v___x_5530_; 
if (v_isShared_5488_ == 0)
{
lean_ctor_set(v___x_5487_, 1, v___x_5528_);
v___x_5530_ = v___x_5487_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v_fst_5485_);
lean_ctor_set(v_reuseFailAlloc_5534_, 1, v___x_5528_);
v___x_5530_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
lean_object* v___x_5532_; 
if (v_isShared_5484_ == 0)
{
lean_ctor_set(v___x_5483_, 1, v___x_5530_);
v___x_5532_ = v___x_5483_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_fst_5481_);
lean_ctor_set(v_reuseFailAlloc_5533_, 1, v___x_5530_);
v___x_5532_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
return v___x_5532_;
}
}
}
}
}
else
{
lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5578_; 
lean_inc(v_stop_5518_);
lean_inc(v_start_5517_);
lean_inc_ref(v_array_5516_);
v_isSharedCheck_5578_ = !lean_is_exclusive(v_fst_5493_);
if (v_isSharedCheck_5578_ == 0)
{
lean_object* v_unused_5579_; lean_object* v_unused_5580_; lean_object* v_unused_5581_; 
v_unused_5579_ = lean_ctor_get(v_fst_5493_, 2);
lean_dec(v_unused_5579_);
v_unused_5580_ = lean_ctor_get(v_fst_5493_, 1);
lean_dec(v_unused_5580_);
v_unused_5581_ = lean_ctor_get(v_fst_5493_, 0);
lean_dec(v_unused_5581_);
v___x_5538_ = v_fst_5493_;
v_isShared_5539_ = v_isSharedCheck_5578_;
goto v_resetjp_5537_;
}
else
{
lean_dec(v_fst_5493_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5578_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5543_; 
v___x_5540_ = lean_array_fget(v_array_5516_, v_start_5517_);
v___x_5541_ = lean_nat_add(v_start_5517_, v___x_5520_);
lean_dec(v_start_5517_);
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 1, v___x_5541_);
v___x_5543_ = v___x_5538_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5577_; 
v_reuseFailAlloc_5577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_array_5516_);
lean_ctor_set(v_reuseFailAlloc_5577_, 1, v___x_5541_);
lean_ctor_set(v_reuseFailAlloc_5577_, 2, v_stop_5518_);
v___x_5543_ = v_reuseFailAlloc_5577_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
uint8_t v___x_5544_; 
v___x_5544_ = lean_unbox(v___x_5540_);
lean_dec(v___x_5540_);
if (v___x_5544_ == 0)
{
lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5550_; 
v___x_5545_ = lean_array_get_size(v_fst_5489_);
v___x_5546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5546_, 0, v___x_5545_);
v___x_5547_ = lean_array_push(v_fst_5481_, v___x_5546_);
v___x_5548_ = lean_array_push(v_fst_5489_, v___x_5519_);
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 1, v___x_5523_);
lean_ctor_set(v___x_5495_, 0, v___x_5543_);
v___x_5550_ = v___x_5495_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v___x_5543_);
lean_ctor_set(v_reuseFailAlloc_5560_, 1, v___x_5523_);
v___x_5550_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
lean_object* v___x_5552_; 
if (v_isShared_5492_ == 0)
{
lean_ctor_set(v___x_5491_, 1, v___x_5550_);
lean_ctor_set(v___x_5491_, 0, v___x_5548_);
v___x_5552_ = v___x_5491_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5559_, 1, v___x_5550_);
v___x_5552_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
lean_object* v___x_5554_; 
if (v_isShared_5488_ == 0)
{
lean_ctor_set(v___x_5487_, 1, v___x_5552_);
v___x_5554_ = v___x_5487_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_fst_5485_);
lean_ctor_set(v_reuseFailAlloc_5558_, 1, v___x_5552_);
v___x_5554_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
lean_object* v___x_5556_; 
if (v_isShared_5484_ == 0)
{
lean_ctor_set(v___x_5483_, 1, v___x_5554_);
lean_ctor_set(v___x_5483_, 0, v___x_5547_);
v___x_5556_ = v___x_5483_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5547_);
lean_ctor_set(v_reuseFailAlloc_5557_, 1, v___x_5554_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
v_a_5472_ = v___x_5556_;
goto v___jp_5471_;
}
}
}
}
}
else
{
lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5566_; 
v___x_5561_ = lean_box(0);
v___x_5562_ = lean_array_push(v_fst_5481_, v___x_5561_);
v___x_5563_ = l_Lean_Expr_fvarId_x21(v___x_5519_);
lean_dec(v___x_5519_);
v___x_5564_ = lean_array_push(v_fst_5485_, v___x_5563_);
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 1, v___x_5523_);
lean_ctor_set(v___x_5495_, 0, v___x_5543_);
v___x_5566_ = v___x_5495_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v___x_5543_);
lean_ctor_set(v_reuseFailAlloc_5576_, 1, v___x_5523_);
v___x_5566_ = v_reuseFailAlloc_5576_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
lean_object* v___x_5568_; 
if (v_isShared_5492_ == 0)
{
lean_ctor_set(v___x_5491_, 1, v___x_5566_);
v___x_5568_ = v___x_5491_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_fst_5489_);
lean_ctor_set(v_reuseFailAlloc_5575_, 1, v___x_5566_);
v___x_5568_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
lean_object* v___x_5570_; 
if (v_isShared_5488_ == 0)
{
lean_ctor_set(v___x_5487_, 1, v___x_5568_);
lean_ctor_set(v___x_5487_, 0, v___x_5564_);
v___x_5570_ = v___x_5487_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v___x_5564_);
lean_ctor_set(v_reuseFailAlloc_5574_, 1, v___x_5568_);
v___x_5570_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
lean_object* v___x_5572_; 
if (v_isShared_5484_ == 0)
{
lean_ctor_set(v___x_5483_, 1, v___x_5570_);
lean_ctor_set(v___x_5483_, 0, v___x_5562_);
v___x_5572_ = v___x_5483_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5562_);
lean_ctor_set(v_reuseFailAlloc_5573_, 1, v___x_5570_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
v_a_5472_ = v___x_5572_;
goto v___jp_5471_;
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
v___jp_5471_:
{
lean_object* v___x_5473_; lean_object* v___x_5474_; 
v___x_5473_ = lean_unsigned_to_nat(1u);
v___x_5474_ = lean_nat_add(v_a_5469_, v___x_5473_);
lean_dec(v_a_5469_);
v_a_5469_ = v___x_5474_;
v_b_5470_ = v_a_5472_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5595_, lean_object* v_a_5596_, lean_object* v_b_5597_){
_start:
{
lean_object* v_res_5598_; 
v_res_5598_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5595_, v_a_5596_, v_b_5597_);
lean_dec(v_upperBound_5595_);
return v_res_5598_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5599_, size_t v_i_5600_, size_t v_stop_5601_){
_start:
{
uint8_t v___x_5602_; 
v___x_5602_ = lean_usize_dec_eq(v_i_5600_, v_stop_5601_);
if (v___x_5602_ == 0)
{
uint8_t v___x_5603_; lean_object* v___x_5604_; uint8_t v___x_5605_; 
v___x_5603_ = 1;
v___x_5604_ = lean_array_uget_borrowed(v_as_5599_, v_i_5600_);
v___x_5605_ = l_Lean_Expr_isFVar(v___x_5604_);
if (v___x_5605_ == 0)
{
return v___x_5603_;
}
else
{
if (v___x_5602_ == 0)
{
size_t v___x_5606_; size_t v___x_5607_; 
v___x_5606_ = ((size_t)1ULL);
v___x_5607_ = lean_usize_add(v_i_5600_, v___x_5606_);
v_i_5600_ = v___x_5607_;
goto _start;
}
else
{
return v___x_5603_;
}
}
}
else
{
uint8_t v___x_5609_; 
v___x_5609_ = 0;
return v___x_5609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5610_, lean_object* v_i_5611_, lean_object* v_stop_5612_){
_start:
{
size_t v_i_boxed_5613_; size_t v_stop_boxed_5614_; uint8_t v_res_5615_; lean_object* v_r_5616_; 
v_i_boxed_5613_ = lean_unbox_usize(v_i_5611_);
lean_dec(v_i_5611_);
v_stop_boxed_5614_ = lean_unbox_usize(v_stop_5612_);
lean_dec(v_stop_5612_);
v_res_5615_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5610_, v_i_boxed_5613_, v_stop_boxed_5614_);
lean_dec_ref(v_as_5610_);
v_r_5616_ = lean_box(v_res_5615_);
return v_r_5616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5617_, size_t v_sz_5618_, size_t v_i_5619_, lean_object* v_bs_5620_){
_start:
{
uint8_t v___x_5621_; 
v___x_5621_ = lean_usize_dec_lt(v_i_5619_, v_sz_5618_);
if (v___x_5621_ == 0)
{
return v_bs_5620_;
}
else
{
lean_object* v_v_5622_; lean_object* v___x_5623_; lean_object* v_bs_x27_5624_; lean_object* v___y_5626_; 
v_v_5622_ = lean_array_uget(v_bs_5620_, v_i_5619_);
v___x_5623_ = lean_unsigned_to_nat(0u);
v_bs_x27_5624_ = lean_array_uset(v_bs_5620_, v_i_5619_, v___x_5623_);
if (lean_obj_tag(v_v_5622_) == 0)
{
v___y_5626_ = v_v_5622_;
goto v___jp_5625_;
}
else
{
lean_object* v_val_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; 
v_val_5631_ = lean_ctor_get(v_v_5622_, 0);
lean_inc(v_val_5631_);
lean_dec_ref(v_v_5622_);
v___x_5632_ = lean_box(0);
v___x_5633_ = lean_array_get_borrowed(v___x_5632_, v___x_5617_, v_val_5631_);
lean_dec(v_val_5631_);
lean_inc(v___x_5633_);
v___y_5626_ = v___x_5633_;
goto v___jp_5625_;
}
v___jp_5625_:
{
size_t v___x_5627_; size_t v___x_5628_; lean_object* v___x_5629_; 
v___x_5627_ = ((size_t)1ULL);
v___x_5628_ = lean_usize_add(v_i_5619_, v___x_5627_);
v___x_5629_ = lean_array_uset(v_bs_x27_5624_, v_i_5619_, v___y_5626_);
v_i_5619_ = v___x_5628_;
v_bs_5620_ = v___x_5629_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5634_, lean_object* v_sz_5635_, lean_object* v_i_5636_, lean_object* v_bs_5637_){
_start:
{
size_t v_sz_boxed_5638_; size_t v_i_boxed_5639_; lean_object* v_res_5640_; 
v_sz_boxed_5638_ = lean_unbox_usize(v_sz_5635_);
lean_dec(v_sz_5635_);
v_i_boxed_5639_ = lean_unbox_usize(v_i_5636_);
lean_dec(v_i_5636_);
v_res_5640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5634_, v_sz_boxed_5638_, v_i_boxed_5639_, v_bs_5637_);
lean_dec_ref(v___x_5634_);
return v_res_5640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5641_, size_t v_sz_5642_, size_t v_i_5643_, lean_object* v_bs_5644_){
_start:
{
uint8_t v___x_5645_; 
v___x_5645_ = lean_usize_dec_lt(v_i_5643_, v_sz_5642_);
if (v___x_5645_ == 0)
{
return v_bs_5644_;
}
else
{
lean_object* v_v_5646_; lean_object* v___x_5647_; lean_object* v_bs_x27_5648_; size_t v_sz_5649_; size_t v___x_5650_; lean_object* v___x_5651_; size_t v___x_5652_; size_t v___x_5653_; lean_object* v___x_5654_; 
v_v_5646_ = lean_array_uget(v_bs_5644_, v_i_5643_);
v___x_5647_ = lean_unsigned_to_nat(0u);
v_bs_x27_5648_ = lean_array_uset(v_bs_5644_, v_i_5643_, v___x_5647_);
v_sz_5649_ = lean_array_size(v_v_5646_);
v___x_5650_ = ((size_t)0ULL);
v___x_5651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5641_, v_sz_5649_, v___x_5650_, v_v_5646_);
v___x_5652_ = ((size_t)1ULL);
v___x_5653_ = lean_usize_add(v_i_5643_, v___x_5652_);
v___x_5654_ = lean_array_uset(v_bs_x27_5648_, v_i_5643_, v___x_5651_);
v_i_5643_ = v___x_5653_;
v_bs_5644_ = v___x_5654_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5656_, lean_object* v_sz_5657_, lean_object* v_i_5658_, lean_object* v_bs_5659_){
_start:
{
size_t v_sz_boxed_5660_; size_t v_i_boxed_5661_; lean_object* v_res_5662_; 
v_sz_boxed_5660_ = lean_unbox_usize(v_sz_5657_);
lean_dec(v_sz_5657_);
v_i_boxed_5661_ = lean_unbox_usize(v_i_5658_);
lean_dec(v_i_5658_);
v_res_5662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5656_, v_sz_boxed_5660_, v_i_boxed_5661_, v_bs_5659_);
lean_dec_ref(v___x_5656_);
return v_res_5662_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; 
v___x_5665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5666_ = lean_unsigned_to_nat(6u);
v___x_5667_ = lean_unsigned_to_nat(463u);
v___x_5668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5669_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5670_ = l_mkPanicMessageWithDecl(v___x_5669_, v___x_5668_, v___x_5667_, v___x_5666_, v___x_5665_);
return v___x_5670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5671_, lean_object* v_as_5672_, size_t v_sz_5673_, size_t v_i_5674_, lean_object* v_b_5675_){
_start:
{
lean_object* v_a_5677_; uint8_t v___x_5681_; 
v___x_5681_ = lean_usize_dec_lt(v_i_5674_, v_sz_5673_);
if (v___x_5681_ == 0)
{
return v_b_5675_;
}
else
{
lean_object* v_a_5682_; lean_object* v___x_5683_; uint8_t v_changed_5684_; 
v_a_5682_ = lean_array_uget_borrowed(v_as_5672_, v_i_5674_);
v___x_5683_ = lean_array_get_size(v___x_5671_);
v_changed_5684_ = lean_nat_dec_lt(v_a_5682_, v___x_5683_);
if (v_changed_5684_ == 0)
{
lean_object* v___x_5685_; lean_object* v___x_5686_; 
lean_dec_ref(v_b_5675_);
v___x_5685_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5686_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5685_);
if (lean_obj_tag(v___x_5686_) == 0)
{
lean_object* v_a_5687_; 
v_a_5687_ = lean_ctor_get(v___x_5686_, 0);
lean_inc(v_a_5687_);
lean_dec_ref(v___x_5686_);
return v_a_5687_;
}
else
{
lean_object* v_a_5688_; 
v_a_5688_ = lean_ctor_get(v___x_5686_, 0);
lean_inc(v_a_5688_);
lean_dec_ref(v___x_5686_);
v_a_5677_ = v_a_5688_;
goto v___jp_5676_;
}
}
else
{
lean_object* v___x_5689_; lean_object* v___x_5690_; 
v___x_5689_ = lean_box(0);
v___x_5690_ = lean_array_get_borrowed(v___x_5689_, v___x_5671_, v_a_5682_);
if (lean_obj_tag(v___x_5690_) == 1)
{
lean_object* v_val_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; 
v_val_5691_ = lean_ctor_get(v___x_5690_, 0);
v___x_5692_ = lean_box(v_changed_5684_);
v___x_5693_ = lean_array_set(v_b_5675_, v_val_5691_, v___x_5692_);
v_a_5677_ = v___x_5693_;
goto v___jp_5676_;
}
else
{
v_a_5677_ = v_b_5675_;
goto v___jp_5676_;
}
}
}
v___jp_5676_:
{
size_t v___x_5678_; size_t v___x_5679_; 
v___x_5678_ = ((size_t)1ULL);
v___x_5679_ = lean_usize_add(v_i_5674_, v___x_5678_);
v_i_5674_ = v___x_5679_;
v_b_5675_ = v_a_5677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5694_, lean_object* v_as_5695_, lean_object* v_sz_5696_, lean_object* v_i_5697_, lean_object* v_b_5698_){
_start:
{
size_t v_sz_boxed_5699_; size_t v_i_boxed_5700_; lean_object* v_res_5701_; 
v_sz_boxed_5699_ = lean_unbox_usize(v_sz_5696_);
lean_dec(v_sz_5696_);
v_i_boxed_5700_ = lean_unbox_usize(v_i_5697_);
lean_dec(v_i_5697_);
v_res_5701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5694_, v_as_5695_, v_sz_boxed_5699_, v_i_boxed_5700_, v_b_5698_);
lean_dec_ref(v_as_5695_);
lean_dec_ref(v___x_5694_);
return v_res_5701_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5702_, lean_object* v_a_5703_, lean_object* v_b_5704_){
_start:
{
uint8_t v___x_5705_; 
v___x_5705_ = lean_nat_dec_lt(v_a_5703_, v_upperBound_5702_);
if (v___x_5705_ == 0)
{
lean_dec(v_a_5703_);
return v_b_5704_;
}
else
{
lean_object* v_snd_5706_; lean_object* v_snd_5707_; lean_object* v_fst_5708_; lean_object* v___x_5710_; uint8_t v_isShared_5711_; uint8_t v_isSharedCheck_5774_; 
v_snd_5706_ = lean_ctor_get(v_b_5704_, 1);
lean_inc(v_snd_5706_);
v_snd_5707_ = lean_ctor_get(v_snd_5706_, 1);
lean_inc(v_snd_5707_);
v_fst_5708_ = lean_ctor_get(v_b_5704_, 0);
v_isSharedCheck_5774_ = !lean_is_exclusive(v_b_5704_);
if (v_isSharedCheck_5774_ == 0)
{
lean_object* v_unused_5775_; 
v_unused_5775_ = lean_ctor_get(v_b_5704_, 1);
lean_dec(v_unused_5775_);
v___x_5710_ = v_b_5704_;
v_isShared_5711_ = v_isSharedCheck_5774_;
goto v_resetjp_5709_;
}
else
{
lean_inc(v_fst_5708_);
lean_dec(v_b_5704_);
v___x_5710_ = lean_box(0);
v_isShared_5711_ = v_isSharedCheck_5774_;
goto v_resetjp_5709_;
}
v_resetjp_5709_:
{
lean_object* v_fst_5712_; lean_object* v___x_5714_; uint8_t v_isShared_5715_; uint8_t v_isSharedCheck_5772_; 
v_fst_5712_ = lean_ctor_get(v_snd_5706_, 0);
v_isSharedCheck_5772_ = !lean_is_exclusive(v_snd_5706_);
if (v_isSharedCheck_5772_ == 0)
{
lean_object* v_unused_5773_; 
v_unused_5773_ = lean_ctor_get(v_snd_5706_, 1);
lean_dec(v_unused_5773_);
v___x_5714_ = v_snd_5706_;
v_isShared_5715_ = v_isSharedCheck_5772_;
goto v_resetjp_5713_;
}
else
{
lean_inc(v_fst_5712_);
lean_dec(v_snd_5706_);
v___x_5714_ = lean_box(0);
v_isShared_5715_ = v_isSharedCheck_5772_;
goto v_resetjp_5713_;
}
v_resetjp_5713_:
{
lean_object* v_array_5716_; lean_object* v_start_5717_; lean_object* v_stop_5718_; uint8_t v___x_5719_; 
v_array_5716_ = lean_ctor_get(v_snd_5707_, 0);
v_start_5717_ = lean_ctor_get(v_snd_5707_, 1);
v_stop_5718_ = lean_ctor_get(v_snd_5707_, 2);
v___x_5719_ = lean_nat_dec_lt(v_start_5717_, v_stop_5718_);
if (v___x_5719_ == 0)
{
lean_object* v___x_5721_; 
lean_dec(v_a_5703_);
if (v_isShared_5715_ == 0)
{
v___x_5721_ = v___x_5714_;
goto v_reusejp_5720_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v_fst_5712_);
lean_ctor_set(v_reuseFailAlloc_5725_, 1, v_snd_5707_);
v___x_5721_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5720_;
}
v_reusejp_5720_:
{
lean_object* v___x_5723_; 
if (v_isShared_5711_ == 0)
{
lean_ctor_set(v___x_5710_, 1, v___x_5721_);
v___x_5723_ = v___x_5710_;
goto v_reusejp_5722_;
}
else
{
lean_object* v_reuseFailAlloc_5724_; 
v_reuseFailAlloc_5724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5724_, 0, v_fst_5708_);
lean_ctor_set(v_reuseFailAlloc_5724_, 1, v___x_5721_);
v___x_5723_ = v_reuseFailAlloc_5724_;
goto v_reusejp_5722_;
}
v_reusejp_5722_:
{
return v___x_5723_;
}
}
}
else
{
lean_object* v___x_5727_; uint8_t v_isShared_5728_; uint8_t v_isSharedCheck_5768_; 
lean_inc(v_stop_5718_);
lean_inc(v_start_5717_);
lean_inc_ref(v_array_5716_);
v_isSharedCheck_5768_ = !lean_is_exclusive(v_snd_5707_);
if (v_isSharedCheck_5768_ == 0)
{
lean_object* v_unused_5769_; lean_object* v_unused_5770_; lean_object* v_unused_5771_; 
v_unused_5769_ = lean_ctor_get(v_snd_5707_, 2);
lean_dec(v_unused_5769_);
v_unused_5770_ = lean_ctor_get(v_snd_5707_, 1);
lean_dec(v_unused_5770_);
v_unused_5771_ = lean_ctor_get(v_snd_5707_, 0);
lean_dec(v_unused_5771_);
v___x_5727_ = v_snd_5707_;
v_isShared_5728_ = v_isSharedCheck_5768_;
goto v_resetjp_5726_;
}
else
{
lean_dec(v_snd_5707_);
v___x_5727_ = lean_box(0);
v_isShared_5728_ = v_isSharedCheck_5768_;
goto v_resetjp_5726_;
}
v_resetjp_5726_:
{
lean_object* v_array_5729_; lean_object* v_start_5730_; lean_object* v_stop_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5736_; 
v_array_5729_ = lean_ctor_get(v_fst_5712_, 0);
v_start_5730_ = lean_ctor_get(v_fst_5712_, 1);
v_stop_5731_ = lean_ctor_get(v_fst_5712_, 2);
v___x_5732_ = lean_array_fget(v_array_5716_, v_start_5717_);
v___x_5733_ = lean_unsigned_to_nat(1u);
v___x_5734_ = lean_nat_add(v_start_5717_, v___x_5733_);
lean_dec(v_start_5717_);
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 1, v___x_5734_);
v___x_5736_ = v___x_5727_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5767_; 
v_reuseFailAlloc_5767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5767_, 0, v_array_5716_);
lean_ctor_set(v_reuseFailAlloc_5767_, 1, v___x_5734_);
lean_ctor_set(v_reuseFailAlloc_5767_, 2, v_stop_5718_);
v___x_5736_ = v_reuseFailAlloc_5767_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
uint8_t v___x_5737_; 
v___x_5737_ = lean_nat_dec_lt(v_start_5730_, v_stop_5731_);
if (v___x_5737_ == 0)
{
lean_object* v___x_5739_; 
lean_dec(v___x_5732_);
lean_dec(v_a_5703_);
if (v_isShared_5715_ == 0)
{
lean_ctor_set(v___x_5714_, 1, v___x_5736_);
v___x_5739_ = v___x_5714_;
goto v_reusejp_5738_;
}
else
{
lean_object* v_reuseFailAlloc_5743_; 
v_reuseFailAlloc_5743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_fst_5712_);
lean_ctor_set(v_reuseFailAlloc_5743_, 1, v___x_5736_);
v___x_5739_ = v_reuseFailAlloc_5743_;
goto v_reusejp_5738_;
}
v_reusejp_5738_:
{
lean_object* v___x_5741_; 
if (v_isShared_5711_ == 0)
{
lean_ctor_set(v___x_5710_, 1, v___x_5739_);
v___x_5741_ = v___x_5710_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5742_; 
v_reuseFailAlloc_5742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5742_, 0, v_fst_5708_);
lean_ctor_set(v_reuseFailAlloc_5742_, 1, v___x_5739_);
v___x_5741_ = v_reuseFailAlloc_5742_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
return v___x_5741_;
}
}
}
else
{
lean_object* v___x_5745_; uint8_t v_isShared_5746_; uint8_t v_isSharedCheck_5763_; 
lean_inc(v_stop_5731_);
lean_inc(v_start_5730_);
lean_inc_ref(v_array_5729_);
v_isSharedCheck_5763_ = !lean_is_exclusive(v_fst_5712_);
if (v_isSharedCheck_5763_ == 0)
{
lean_object* v_unused_5764_; lean_object* v_unused_5765_; lean_object* v_unused_5766_; 
v_unused_5764_ = lean_ctor_get(v_fst_5712_, 2);
lean_dec(v_unused_5764_);
v_unused_5765_ = lean_ctor_get(v_fst_5712_, 1);
lean_dec(v_unused_5765_);
v_unused_5766_ = lean_ctor_get(v_fst_5712_, 0);
lean_dec(v_unused_5766_);
v___x_5745_ = v_fst_5712_;
v_isShared_5746_ = v_isSharedCheck_5763_;
goto v_resetjp_5744_;
}
else
{
lean_dec(v_fst_5712_);
v___x_5745_ = lean_box(0);
v_isShared_5746_ = v_isSharedCheck_5763_;
goto v_resetjp_5744_;
}
v_resetjp_5744_:
{
lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5750_; 
v___x_5747_ = lean_array_fget(v_array_5729_, v_start_5730_);
v___x_5748_ = lean_nat_add(v_start_5730_, v___x_5733_);
lean_dec(v_start_5730_);
if (v_isShared_5746_ == 0)
{
lean_ctor_set(v___x_5745_, 1, v___x_5748_);
v___x_5750_ = v___x_5745_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5762_; 
v_reuseFailAlloc_5762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5762_, 0, v_array_5729_);
lean_ctor_set(v_reuseFailAlloc_5762_, 1, v___x_5748_);
lean_ctor_set(v_reuseFailAlloc_5762_, 2, v_stop_5731_);
v___x_5750_ = v_reuseFailAlloc_5762_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
size_t v_sz_5751_; size_t v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5755_; 
v_sz_5751_ = lean_array_size(v___x_5747_);
v___x_5752_ = ((size_t)0ULL);
v___x_5753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5732_, v___x_5747_, v_sz_5751_, v___x_5752_, v_fst_5708_);
lean_dec(v___x_5747_);
lean_dec(v___x_5732_);
if (v_isShared_5715_ == 0)
{
lean_ctor_set(v___x_5714_, 1, v___x_5736_);
lean_ctor_set(v___x_5714_, 0, v___x_5750_);
v___x_5755_ = v___x_5714_;
goto v_reusejp_5754_;
}
else
{
lean_object* v_reuseFailAlloc_5761_; 
v_reuseFailAlloc_5761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5761_, 0, v___x_5750_);
lean_ctor_set(v_reuseFailAlloc_5761_, 1, v___x_5736_);
v___x_5755_ = v_reuseFailAlloc_5761_;
goto v_reusejp_5754_;
}
v_reusejp_5754_:
{
lean_object* v___x_5757_; 
if (v_isShared_5711_ == 0)
{
lean_ctor_set(v___x_5710_, 1, v___x_5755_);
lean_ctor_set(v___x_5710_, 0, v___x_5753_);
v___x_5757_ = v___x_5710_;
goto v_reusejp_5756_;
}
else
{
lean_object* v_reuseFailAlloc_5760_; 
v_reuseFailAlloc_5760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5760_, 0, v___x_5753_);
lean_ctor_set(v_reuseFailAlloc_5760_, 1, v___x_5755_);
v___x_5757_ = v_reuseFailAlloc_5760_;
goto v_reusejp_5756_;
}
v_reusejp_5756_:
{
lean_object* v___x_5758_; 
v___x_5758_ = lean_nat_add(v_a_5703_, v___x_5733_);
lean_dec(v_a_5703_);
v_a_5703_ = v___x_5758_;
v_b_5704_ = v___x_5757_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_5776_, lean_object* v_a_5777_, lean_object* v_b_5778_){
_start:
{
lean_object* v_res_5779_; 
v_res_5779_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_5776_, v_a_5777_, v_b_5778_);
lean_dec(v_upperBound_5776_);
return v_res_5779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5780_, uint8_t v___x_5781_, lean_object* v_as_5782_, size_t v_sz_5783_, size_t v_i_5784_, lean_object* v_b_5785_){
_start:
{
lean_object* v_a_5787_; uint8_t v___x_5791_; 
v___x_5791_ = lean_usize_dec_lt(v_i_5784_, v_sz_5783_);
if (v___x_5791_ == 0)
{
return v_b_5785_;
}
else
{
lean_object* v_fst_5792_; lean_object* v_snd_5793_; lean_object* v___x_5795_; uint8_t v_isShared_5796_; uint8_t v_isSharedCheck_5814_; 
v_fst_5792_ = lean_ctor_get(v_b_5785_, 0);
v_snd_5793_ = lean_ctor_get(v_b_5785_, 1);
v_isSharedCheck_5814_ = !lean_is_exclusive(v_b_5785_);
if (v_isSharedCheck_5814_ == 0)
{
v___x_5795_ = v_b_5785_;
v_isShared_5796_ = v_isSharedCheck_5814_;
goto v_resetjp_5794_;
}
else
{
lean_inc(v_snd_5793_);
lean_inc(v_fst_5792_);
lean_dec(v_b_5785_);
v___x_5795_ = lean_box(0);
v_isShared_5796_ = v_isSharedCheck_5814_;
goto v_resetjp_5794_;
}
v_resetjp_5794_:
{
lean_object* v_a_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; 
v_a_5801_ = lean_array_uget_borrowed(v_as_5782_, v_i_5784_);
v___x_5802_ = lean_box(0);
v___x_5803_ = lean_array_get_borrowed(v___x_5802_, v___x_5780_, v_a_5801_);
if (lean_obj_tag(v___x_5803_) == 1)
{
lean_object* v_val_5804_; uint8_t v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; uint8_t v___x_5808_; 
v_val_5804_ = lean_ctor_get(v___x_5803_, 0);
v___x_5805_ = 0;
v___x_5806_ = lean_box(v___x_5805_);
v___x_5807_ = lean_array_get(v___x_5806_, v_fst_5792_, v_val_5804_);
lean_dec(v___x_5806_);
v___x_5808_ = lean_unbox(v___x_5807_);
lean_dec(v___x_5807_);
if (v___x_5808_ == 0)
{
if (v___x_5781_ == 0)
{
goto v___jp_5797_;
}
else
{
lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; 
lean_del_object(v___x_5795_);
lean_dec(v_snd_5793_);
v___x_5809_ = lean_box(v___x_5781_);
v___x_5810_ = lean_array_set(v_fst_5792_, v_val_5804_, v___x_5809_);
v___x_5811_ = lean_box(v___x_5781_);
v___x_5812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5812_, 0, v___x_5810_);
lean_ctor_set(v___x_5812_, 1, v___x_5811_);
v_a_5787_ = v___x_5812_;
goto v___jp_5786_;
}
}
else
{
goto v___jp_5797_;
}
}
else
{
lean_object* v___x_5813_; 
lean_del_object(v___x_5795_);
v___x_5813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5813_, 0, v_fst_5792_);
lean_ctor_set(v___x_5813_, 1, v_snd_5793_);
v_a_5787_ = v___x_5813_;
goto v___jp_5786_;
}
v___jp_5797_:
{
lean_object* v___x_5799_; 
if (v_isShared_5796_ == 0)
{
v___x_5799_ = v___x_5795_;
goto v_reusejp_5798_;
}
else
{
lean_object* v_reuseFailAlloc_5800_; 
v_reuseFailAlloc_5800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5800_, 0, v_fst_5792_);
lean_ctor_set(v_reuseFailAlloc_5800_, 1, v_snd_5793_);
v___x_5799_ = v_reuseFailAlloc_5800_;
goto v_reusejp_5798_;
}
v_reusejp_5798_:
{
v_a_5787_ = v___x_5799_;
goto v___jp_5786_;
}
}
}
}
v___jp_5786_:
{
size_t v___x_5788_; size_t v___x_5789_; 
v___x_5788_ = ((size_t)1ULL);
v___x_5789_ = lean_usize_add(v_i_5784_, v___x_5788_);
v_i_5784_ = v___x_5789_;
v_b_5785_ = v_a_5787_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5815_, lean_object* v___x_5816_, lean_object* v_as_5817_, lean_object* v_sz_5818_, lean_object* v_i_5819_, lean_object* v_b_5820_){
_start:
{
uint8_t v___x_8471__boxed_5821_; size_t v_sz_boxed_5822_; size_t v_i_boxed_5823_; lean_object* v_res_5824_; 
v___x_8471__boxed_5821_ = lean_unbox(v___x_5816_);
v_sz_boxed_5822_ = lean_unbox_usize(v_sz_5818_);
lean_dec(v_sz_5818_);
v_i_boxed_5823_ = lean_unbox_usize(v_i_5819_);
lean_dec(v_i_5819_);
v_res_5824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5815_, v___x_8471__boxed_5821_, v_as_5817_, v_sz_boxed_5822_, v_i_boxed_5823_, v_b_5820_);
lean_dec_ref(v_as_5817_);
lean_dec_ref(v___x_5815_);
return v_res_5824_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5825_, lean_object* v___x_5826_, lean_object* v_fixedParamPerms_5827_, lean_object* v_next_5828_, lean_object* v_a_5829_, lean_object* v_b_5830_){
_start:
{
lean_object* v_a_5832_; uint8_t v___x_5836_; 
v___x_5836_ = lean_nat_dec_lt(v_a_5829_, v_upperBound_5825_);
if (v___x_5836_ == 0)
{
lean_dec(v_a_5829_);
return v_b_5830_;
}
else
{
lean_object* v_fst_5837_; lean_object* v_snd_5838_; lean_object* v___x_5840_; uint8_t v_isShared_5841_; uint8_t v_isSharedCheck_5874_; 
v_fst_5837_ = lean_ctor_get(v_b_5830_, 0);
v_snd_5838_ = lean_ctor_get(v_b_5830_, 1);
v_isSharedCheck_5874_ = !lean_is_exclusive(v_b_5830_);
if (v_isSharedCheck_5874_ == 0)
{
v___x_5840_ = v_b_5830_;
v_isShared_5841_ = v_isSharedCheck_5874_;
goto v_resetjp_5839_;
}
else
{
lean_inc(v_snd_5838_);
lean_inc(v_fst_5837_);
lean_dec(v_b_5830_);
v___x_5840_ = lean_box(0);
v_isShared_5841_ = v_isSharedCheck_5874_;
goto v_resetjp_5839_;
}
v_resetjp_5839_:
{
lean_object* v___x_5842_; 
v___x_5842_ = lean_array_fget_borrowed(v___x_5826_, v_a_5829_);
if (lean_obj_tag(v___x_5842_) == 1)
{
lean_object* v_val_5843_; uint8_t v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; uint8_t v___x_5847_; 
v_val_5843_ = lean_ctor_get(v___x_5842_, 0);
v___x_5844_ = 0;
v___x_5845_ = lean_box(v___x_5844_);
v___x_5846_ = lean_array_get(v___x_5845_, v_fst_5837_, v_val_5843_);
lean_dec(v___x_5845_);
v___x_5847_ = lean_unbox(v___x_5846_);
if (v___x_5847_ == 0)
{
lean_object* v___x_5849_; 
lean_dec(v___x_5846_);
if (v_isShared_5841_ == 0)
{
v___x_5849_ = v___x_5840_;
goto v_reusejp_5848_;
}
else
{
lean_object* v_reuseFailAlloc_5850_; 
v_reuseFailAlloc_5850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_fst_5837_);
lean_ctor_set(v_reuseFailAlloc_5850_, 1, v_snd_5838_);
v___x_5849_ = v_reuseFailAlloc_5850_;
goto v_reusejp_5848_;
}
v_reusejp_5848_:
{
v_a_5832_ = v___x_5849_;
goto v___jp_5831_;
}
}
else
{
lean_object* v_revDeps_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; lean_object* v___x_5856_; 
v_revDeps_5851_ = lean_ctor_get(v_fixedParamPerms_5827_, 2);
v___x_5852_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_5853_ = lean_array_get_borrowed(v___x_5852_, v_revDeps_5851_, v_next_5828_);
v___x_5854_ = lean_array_get_borrowed(v___x_5852_, v___x_5853_, v_a_5829_);
if (v_isShared_5841_ == 0)
{
v___x_5856_ = v___x_5840_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5870_; 
v_reuseFailAlloc_5870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5870_, 0, v_fst_5837_);
lean_ctor_set(v_reuseFailAlloc_5870_, 1, v_snd_5838_);
v___x_5856_ = v_reuseFailAlloc_5870_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
size_t v_sz_5857_; size_t v___x_5858_; uint8_t v___x_5859_; lean_object* v___x_5860_; lean_object* v_fst_5861_; lean_object* v_snd_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5869_; 
v_sz_5857_ = lean_array_size(v___x_5854_);
v___x_5858_ = ((size_t)0ULL);
v___x_5859_ = lean_unbox(v___x_5846_);
lean_dec(v___x_5846_);
v___x_5860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5826_, v___x_5859_, v___x_5854_, v_sz_5857_, v___x_5858_, v___x_5856_);
v_fst_5861_ = lean_ctor_get(v___x_5860_, 0);
v_snd_5862_ = lean_ctor_get(v___x_5860_, 1);
v_isSharedCheck_5869_ = !lean_is_exclusive(v___x_5860_);
if (v_isSharedCheck_5869_ == 0)
{
v___x_5864_ = v___x_5860_;
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_snd_5862_);
lean_inc(v_fst_5861_);
lean_dec(v___x_5860_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v___x_5867_; 
if (v_isShared_5865_ == 0)
{
v___x_5867_ = v___x_5864_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v_fst_5861_);
lean_ctor_set(v_reuseFailAlloc_5868_, 1, v_snd_5862_);
v___x_5867_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
v_a_5832_ = v___x_5867_;
goto v___jp_5831_;
}
}
}
}
}
else
{
lean_object* v___x_5872_; 
if (v_isShared_5841_ == 0)
{
v___x_5872_ = v___x_5840_;
goto v_reusejp_5871_;
}
else
{
lean_object* v_reuseFailAlloc_5873_; 
v_reuseFailAlloc_5873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_fst_5837_);
lean_ctor_set(v_reuseFailAlloc_5873_, 1, v_snd_5838_);
v___x_5872_ = v_reuseFailAlloc_5873_;
goto v_reusejp_5871_;
}
v_reusejp_5871_:
{
v_a_5832_ = v___x_5872_;
goto v___jp_5831_;
}
}
}
}
v___jp_5831_:
{
lean_object* v___x_5833_; lean_object* v___x_5834_; 
v___x_5833_ = lean_unsigned_to_nat(1u);
v___x_5834_ = lean_nat_add(v_a_5829_, v___x_5833_);
lean_dec(v_a_5829_);
v_a_5829_ = v___x_5834_;
v_b_5830_ = v_a_5832_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5875_, lean_object* v___x_5876_, lean_object* v_fixedParamPerms_5877_, lean_object* v_next_5878_, lean_object* v_a_5879_, lean_object* v_b_5880_){
_start:
{
lean_object* v_res_5881_; 
v_res_5881_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5875_, v___x_5876_, v_fixedParamPerms_5877_, v_next_5878_, v_a_5879_, v_b_5880_);
lean_dec(v_next_5878_);
lean_dec_ref(v_fixedParamPerms_5877_);
lean_dec_ref(v___x_5876_);
lean_dec(v_upperBound_5875_);
return v_res_5881_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5882_, lean_object* v___x_5883_, lean_object* v_fixedParamPerms_5884_, lean_object* v_a_5885_, lean_object* v_b_5886_){
_start:
{
uint8_t v___x_5887_; 
v___x_5887_ = lean_nat_dec_lt(v_a_5885_, v_upperBound_5882_);
if (v___x_5887_ == 0)
{
lean_dec(v_a_5885_);
return v_b_5886_;
}
else
{
lean_object* v_fst_5888_; lean_object* v_snd_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5912_; 
v_fst_5888_ = lean_ctor_get(v_b_5886_, 0);
v_snd_5889_ = lean_ctor_get(v_b_5886_, 1);
v_isSharedCheck_5912_ = !lean_is_exclusive(v_b_5886_);
if (v_isSharedCheck_5912_ == 0)
{
v___x_5891_ = v_b_5886_;
v_isShared_5892_ = v_isSharedCheck_5912_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_snd_5889_);
lean_inc(v_fst_5888_);
lean_dec(v_b_5886_);
v___x_5891_ = lean_box(0);
v_isShared_5892_ = v_isSharedCheck_5912_;
goto v_resetjp_5890_;
}
v_resetjp_5890_:
{
lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5897_; 
v___x_5893_ = lean_array_fget_borrowed(v___x_5883_, v_a_5885_);
v___x_5894_ = lean_array_get_size(v___x_5893_);
v___x_5895_ = lean_unsigned_to_nat(0u);
if (v_isShared_5892_ == 0)
{
v___x_5897_ = v___x_5891_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_5911_; 
v_reuseFailAlloc_5911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5911_, 0, v_fst_5888_);
lean_ctor_set(v_reuseFailAlloc_5911_, 1, v_snd_5889_);
v___x_5897_ = v_reuseFailAlloc_5911_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
lean_object* v___x_5898_; lean_object* v_fst_5899_; lean_object* v_snd_5900_; lean_object* v___x_5902_; uint8_t v_isShared_5903_; uint8_t v_isSharedCheck_5910_; 
v___x_5898_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5894_, v___x_5893_, v_fixedParamPerms_5884_, v_a_5885_, v___x_5895_, v___x_5897_);
v_fst_5899_ = lean_ctor_get(v___x_5898_, 0);
v_snd_5900_ = lean_ctor_get(v___x_5898_, 1);
v_isSharedCheck_5910_ = !lean_is_exclusive(v___x_5898_);
if (v_isSharedCheck_5910_ == 0)
{
v___x_5902_ = v___x_5898_;
v_isShared_5903_ = v_isSharedCheck_5910_;
goto v_resetjp_5901_;
}
else
{
lean_inc(v_snd_5900_);
lean_inc(v_fst_5899_);
lean_dec(v___x_5898_);
v___x_5902_ = lean_box(0);
v_isShared_5903_ = v_isSharedCheck_5910_;
goto v_resetjp_5901_;
}
v_resetjp_5901_:
{
lean_object* v___x_5905_; 
if (v_isShared_5903_ == 0)
{
v___x_5905_ = v___x_5902_;
goto v_reusejp_5904_;
}
else
{
lean_object* v_reuseFailAlloc_5909_; 
v_reuseFailAlloc_5909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5909_, 0, v_fst_5899_);
lean_ctor_set(v_reuseFailAlloc_5909_, 1, v_snd_5900_);
v___x_5905_ = v_reuseFailAlloc_5909_;
goto v_reusejp_5904_;
}
v_reusejp_5904_:
{
lean_object* v___x_5906_; lean_object* v___x_5907_; 
v___x_5906_ = lean_unsigned_to_nat(1u);
v___x_5907_ = lean_nat_add(v_a_5885_, v___x_5906_);
lean_dec(v_a_5885_);
v_a_5885_ = v___x_5907_;
v_b_5886_ = v___x_5905_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5913_, lean_object* v___x_5914_, lean_object* v_fixedParamPerms_5915_, lean_object* v_a_5916_, lean_object* v_b_5917_){
_start:
{
lean_object* v_res_5918_; 
v_res_5918_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5913_, v___x_5914_, v_fixedParamPerms_5915_, v_a_5916_, v_b_5917_);
lean_dec_ref(v_fixedParamPerms_5915_);
lean_dec_ref(v___x_5914_);
lean_dec(v_upperBound_5913_);
return v_res_5918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_5919_, lean_object* v___x_5920_, lean_object* v_fixedParamPerms_5921_, lean_object* v_b_5922_){
_start:
{
lean_object* v_snd_5923_; uint8_t v___x_5924_; 
v_snd_5923_ = lean_ctor_get(v_b_5922_, 1);
v___x_5924_ = lean_unbox(v_snd_5923_);
if (v___x_5924_ == 0)
{
lean_object* v_fst_5925_; lean_object* v___x_5927_; uint8_t v_isShared_5928_; uint8_t v_isSharedCheck_5932_; 
lean_inc(v_snd_5923_);
v_fst_5925_ = lean_ctor_get(v_b_5922_, 0);
v_isSharedCheck_5932_ = !lean_is_exclusive(v_b_5922_);
if (v_isSharedCheck_5932_ == 0)
{
lean_object* v_unused_5933_; 
v_unused_5933_ = lean_ctor_get(v_b_5922_, 1);
lean_dec(v_unused_5933_);
v___x_5927_ = v_b_5922_;
v_isShared_5928_ = v_isSharedCheck_5932_;
goto v_resetjp_5926_;
}
else
{
lean_inc(v_fst_5925_);
lean_dec(v_b_5922_);
v___x_5927_ = lean_box(0);
v_isShared_5928_ = v_isSharedCheck_5932_;
goto v_resetjp_5926_;
}
v_resetjp_5926_:
{
lean_object* v___x_5930_; 
if (v_isShared_5928_ == 0)
{
v___x_5930_ = v___x_5927_;
goto v_reusejp_5929_;
}
else
{
lean_object* v_reuseFailAlloc_5931_; 
v_reuseFailAlloc_5931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5931_, 0, v_fst_5925_);
lean_ctor_set(v_reuseFailAlloc_5931_, 1, v_snd_5923_);
v___x_5930_ = v_reuseFailAlloc_5931_;
goto v_reusejp_5929_;
}
v_reusejp_5929_:
{
return v___x_5930_;
}
}
}
else
{
lean_object* v_fst_5934_; lean_object* v___x_5936_; uint8_t v_isShared_5937_; uint8_t v_isSharedCheck_5955_; 
v_fst_5934_ = lean_ctor_get(v_b_5922_, 0);
v_isSharedCheck_5955_ = !lean_is_exclusive(v_b_5922_);
if (v_isSharedCheck_5955_ == 0)
{
lean_object* v_unused_5956_; 
v_unused_5956_ = lean_ctor_get(v_b_5922_, 1);
lean_dec(v_unused_5956_);
v___x_5936_ = v_b_5922_;
v_isShared_5937_ = v_isSharedCheck_5955_;
goto v_resetjp_5935_;
}
else
{
lean_inc(v_fst_5934_);
lean_dec(v_b_5922_);
v___x_5936_ = lean_box(0);
v_isShared_5937_ = v_isSharedCheck_5955_;
goto v_resetjp_5935_;
}
v_resetjp_5935_:
{
uint8_t v_changed_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5942_; 
v_changed_5938_ = 0;
v___x_5939_ = lean_unsigned_to_nat(0u);
v___x_5940_ = lean_box(v_changed_5938_);
if (v_isShared_5937_ == 0)
{
lean_ctor_set(v___x_5936_, 1, v___x_5940_);
v___x_5942_ = v___x_5936_;
goto v_reusejp_5941_;
}
else
{
lean_object* v_reuseFailAlloc_5954_; 
v_reuseFailAlloc_5954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5954_, 0, v_fst_5934_);
lean_ctor_set(v_reuseFailAlloc_5954_, 1, v___x_5940_);
v___x_5942_ = v_reuseFailAlloc_5954_;
goto v_reusejp_5941_;
}
v_reusejp_5941_:
{
lean_object* v___x_5943_; lean_object* v_fst_5944_; lean_object* v_snd_5945_; lean_object* v___x_5947_; uint8_t v_isShared_5948_; uint8_t v_isSharedCheck_5953_; 
v___x_5943_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5919_, v___x_5920_, v_fixedParamPerms_5921_, v___x_5939_, v___x_5942_);
v_fst_5944_ = lean_ctor_get(v___x_5943_, 0);
v_snd_5945_ = lean_ctor_get(v___x_5943_, 1);
v_isSharedCheck_5953_ = !lean_is_exclusive(v___x_5943_);
if (v_isSharedCheck_5953_ == 0)
{
v___x_5947_ = v___x_5943_;
v_isShared_5948_ = v_isSharedCheck_5953_;
goto v_resetjp_5946_;
}
else
{
lean_inc(v_snd_5945_);
lean_inc(v_fst_5944_);
lean_dec(v___x_5943_);
v___x_5947_ = lean_box(0);
v_isShared_5948_ = v_isSharedCheck_5953_;
goto v_resetjp_5946_;
}
v_resetjp_5946_:
{
lean_object* v___x_5950_; 
if (v_isShared_5948_ == 0)
{
v___x_5950_ = v___x_5947_;
goto v_reusejp_5949_;
}
else
{
lean_object* v_reuseFailAlloc_5952_; 
v_reuseFailAlloc_5952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_fst_5944_);
lean_ctor_set(v_reuseFailAlloc_5952_, 1, v_snd_5945_);
v___x_5950_ = v_reuseFailAlloc_5952_;
goto v_reusejp_5949_;
}
v_reusejp_5949_:
{
v_b_5922_ = v___x_5950_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_5957_, lean_object* v___x_5958_, lean_object* v_fixedParamPerms_5959_, lean_object* v_b_5960_){
_start:
{
lean_object* v_res_5961_; 
v_res_5961_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_5957_, v___x_5958_, v_fixedParamPerms_5959_, v_b_5960_);
lean_dec_ref(v_fixedParamPerms_5959_);
lean_dec_ref(v___x_5958_);
lean_dec(v___x_5957_);
return v_res_5961_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; 
v___x_5963_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_5964_ = lean_unsigned_to_nat(2u);
v___x_5965_ = lean_unsigned_to_nat(457u);
v___x_5966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5967_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5968_ = l_mkPanicMessageWithDecl(v___x_5967_, v___x_5966_, v___x_5965_, v___x_5964_, v___x_5963_);
return v___x_5968_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; 
v___x_5970_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_5971_ = lean_unsigned_to_nat(2u);
v___x_5972_ = lean_unsigned_to_nat(458u);
v___x_5973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5974_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5975_ = l_mkPanicMessageWithDecl(v___x_5974_, v___x_5973_, v___x_5972_, v___x_5971_, v___x_5970_);
return v___x_5975_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; 
v___x_5977_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_5978_ = lean_unsigned_to_nat(2u);
v___x_5979_ = lean_unsigned_to_nat(456u);
v___x_5980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5981_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5982_ = l_mkPanicMessageWithDecl(v___x_5981_, v___x_5980_, v___x_5979_, v___x_5978_, v___x_5977_);
return v___x_5982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_5983_, lean_object* v_xs_5984_, lean_object* v_toErase_5985_){
_start:
{
lean_object* v___x_5986_; lean_object* v___x_5987_; uint8_t v___x_6071_; 
v___x_5986_ = lean_unsigned_to_nat(0u);
v___x_5987_ = lean_array_get_size(v_xs_5984_);
v___x_6071_ = lean_nat_dec_lt(v___x_5986_, v___x_5987_);
if (v___x_6071_ == 0)
{
goto v___jp_5988_;
}
else
{
if (v___x_6071_ == 0)
{
goto v___jp_5988_;
}
else
{
size_t v___x_6072_; size_t v___x_6073_; uint8_t v___x_6074_; 
v___x_6072_ = ((size_t)0ULL);
v___x_6073_ = lean_usize_of_nat(v___x_5987_);
v___x_6074_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_5984_, v___x_6072_, v___x_6073_);
if (v___x_6074_ == 0)
{
goto v___jp_5988_;
}
else
{
lean_object* v___x_6075_; lean_object* v___x_6076_; 
lean_dec_ref(v_toErase_5985_);
lean_dec_ref(v_xs_5984_);
lean_dec_ref(v_fixedParamPerms_5983_);
v___x_6075_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6076_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6075_);
return v___x_6076_;
}
}
}
v___jp_5988_:
{
lean_object* v_numFixed_5989_; lean_object* v_perms_5990_; lean_object* v_revDeps_5991_; uint8_t v___x_5992_; 
v_numFixed_5989_ = lean_ctor_get(v_fixedParamPerms_5983_, 0);
v_perms_5990_ = lean_ctor_get(v_fixedParamPerms_5983_, 1);
lean_inc_ref(v_perms_5990_);
v_revDeps_5991_ = lean_ctor_get(v_fixedParamPerms_5983_, 2);
lean_inc_ref(v_revDeps_5991_);
v___x_5992_ = lean_nat_dec_eq(v_numFixed_5989_, v___x_5987_);
if (v___x_5992_ == 0)
{
lean_object* v___x_5993_; lean_object* v___x_5994_; 
lean_dec_ref(v_revDeps_5991_);
lean_dec_ref(v_perms_5990_);
lean_dec_ref(v_toErase_5985_);
lean_dec_ref(v_xs_5984_);
lean_dec_ref(v_fixedParamPerms_5983_);
v___x_5993_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_5994_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_5993_);
return v___x_5994_;
}
else
{
lean_object* v___x_5995_; lean_object* v___x_5996_; uint8_t v_changed_5997_; 
v___x_5995_ = lean_array_get_size(v_toErase_5985_);
v___x_5996_ = lean_array_get_size(v_perms_5990_);
v_changed_5997_ = lean_nat_dec_eq(v___x_5995_, v___x_5996_);
if (v_changed_5997_ == 0)
{
lean_object* v___x_5998_; lean_object* v___x_5999_; 
lean_dec_ref(v_revDeps_5991_);
lean_dec_ref(v_perms_5990_);
lean_dec_ref(v_toErase_5985_);
lean_dec_ref(v_xs_5984_);
lean_dec_ref(v_fixedParamPerms_5983_);
v___x_5998_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_5999_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_5998_);
return v___x_5999_;
}
else
{
uint8_t v_changed_6000_; lean_object* v___x_6001_; lean_object* v_mask_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v_fst_6008_; lean_object* v___x_6010_; uint8_t v_isShared_6011_; uint8_t v_isSharedCheck_6069_; 
v_changed_6000_ = 0;
v___x_6001_ = lean_box(v_changed_6000_);
lean_inc(v_numFixed_5989_);
v_mask_6002_ = lean_mk_array(v_numFixed_5989_, v___x_6001_);
v___x_6003_ = l_Array_toSubarray___redArg(v_toErase_5985_, v___x_5986_, v___x_5995_);
lean_inc_ref(v_perms_5990_);
v___x_6004_ = l_Array_toSubarray___redArg(v_perms_5990_, v___x_5986_, v___x_5996_);
v___x_6005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6005_, 0, v___x_6003_);
lean_ctor_set(v___x_6005_, 1, v___x_6004_);
v___x_6006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6006_, 0, v_mask_6002_);
lean_ctor_set(v___x_6006_, 1, v___x_6005_);
v___x_6007_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_5995_, v___x_5986_, v___x_6006_);
v_fst_6008_ = lean_ctor_get(v___x_6007_, 0);
v_isSharedCheck_6069_ = !lean_is_exclusive(v___x_6007_);
if (v_isSharedCheck_6069_ == 0)
{
lean_object* v_unused_6070_; 
v_unused_6070_ = lean_ctor_get(v___x_6007_, 1);
lean_dec(v_unused_6070_);
v___x_6010_ = v___x_6007_;
v_isShared_6011_ = v_isSharedCheck_6069_;
goto v_resetjp_6009_;
}
else
{
lean_inc(v_fst_6008_);
lean_dec(v___x_6007_);
v___x_6010_ = lean_box(0);
v_isShared_6011_ = v_isSharedCheck_6069_;
goto v_resetjp_6009_;
}
v_resetjp_6009_:
{
lean_object* v___x_6012_; lean_object* v___x_6014_; 
v___x_6012_ = lean_box(v_changed_5997_);
if (v_isShared_6011_ == 0)
{
lean_ctor_set(v___x_6010_, 1, v___x_6012_);
v___x_6014_ = v___x_6010_;
goto v_reusejp_6013_;
}
else
{
lean_object* v_reuseFailAlloc_6068_; 
v_reuseFailAlloc_6068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6068_, 0, v_fst_6008_);
lean_ctor_set(v_reuseFailAlloc_6068_, 1, v___x_6012_);
v___x_6014_ = v_reuseFailAlloc_6068_;
goto v_reusejp_6013_;
}
v_reusejp_6013_:
{
lean_object* v___x_6015_; lean_object* v___x_6017_; uint8_t v_isShared_6018_; uint8_t v_isSharedCheck_6064_; 
v___x_6015_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_5996_, v_perms_5990_, v_fixedParamPerms_5983_, v___x_6014_);
v_isSharedCheck_6064_ = !lean_is_exclusive(v_fixedParamPerms_5983_);
if (v_isSharedCheck_6064_ == 0)
{
lean_object* v_unused_6065_; lean_object* v_unused_6066_; lean_object* v_unused_6067_; 
v_unused_6065_ = lean_ctor_get(v_fixedParamPerms_5983_, 2);
lean_dec(v_unused_6065_);
v_unused_6066_ = lean_ctor_get(v_fixedParamPerms_5983_, 1);
lean_dec(v_unused_6066_);
v_unused_6067_ = lean_ctor_get(v_fixedParamPerms_5983_, 0);
lean_dec(v_unused_6067_);
v___x_6017_ = v_fixedParamPerms_5983_;
v_isShared_6018_ = v_isSharedCheck_6064_;
goto v_resetjp_6016_;
}
else
{
lean_dec(v_fixedParamPerms_5983_);
v___x_6017_ = lean_box(0);
v_isShared_6018_ = v_isSharedCheck_6064_;
goto v_resetjp_6016_;
}
v_resetjp_6016_:
{
lean_object* v_fst_6019_; lean_object* v___x_6021_; uint8_t v_isShared_6022_; uint8_t v_isSharedCheck_6062_; 
v_fst_6019_ = lean_ctor_get(v___x_6015_, 0);
v_isSharedCheck_6062_ = !lean_is_exclusive(v___x_6015_);
if (v_isSharedCheck_6062_ == 0)
{
lean_object* v_unused_6063_; 
v_unused_6063_ = lean_ctor_get(v___x_6015_, 1);
lean_dec(v_unused_6063_);
v___x_6021_ = v___x_6015_;
v_isShared_6022_ = v_isSharedCheck_6062_;
goto v_resetjp_6020_;
}
else
{
lean_inc(v_fst_6019_);
lean_dec(v___x_6015_);
v___x_6021_ = lean_box(0);
v_isShared_6022_ = v_isSharedCheck_6062_;
goto v_resetjp_6020_;
}
v_resetjp_6020_:
{
lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6028_; 
v___x_6023_ = lean_array_get_size(v_fst_6019_);
v___x_6024_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6025_ = l_Array_toSubarray___redArg(v_fst_6019_, v___x_5986_, v___x_6023_);
v___x_6026_ = l_Array_toSubarray___redArg(v_xs_5984_, v___x_5986_, v___x_5987_);
if (v_isShared_6022_ == 0)
{
lean_ctor_set(v___x_6021_, 1, v___x_6026_);
lean_ctor_set(v___x_6021_, 0, v___x_6025_);
v___x_6028_ = v___x_6021_;
goto v_reusejp_6027_;
}
else
{
lean_object* v_reuseFailAlloc_6061_; 
v_reuseFailAlloc_6061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6061_, 0, v___x_6025_);
lean_ctor_set(v_reuseFailAlloc_6061_, 1, v___x_6026_);
v___x_6028_ = v_reuseFailAlloc_6061_;
goto v_reusejp_6027_;
}
v_reusejp_6027_:
{
lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v_snd_6033_; lean_object* v_snd_6034_; lean_object* v_fst_6035_; lean_object* v_fst_6036_; lean_object* v___x_6038_; uint8_t v_isShared_6039_; uint8_t v_isSharedCheck_6059_; 
v___x_6029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6024_);
lean_ctor_set(v___x_6029_, 1, v___x_6028_);
v___x_6030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6024_);
lean_ctor_set(v___x_6030_, 1, v___x_6029_);
v___x_6031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6024_);
lean_ctor_set(v___x_6031_, 1, v___x_6030_);
v___x_6032_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6023_, v___x_5986_, v___x_6031_);
v_snd_6033_ = lean_ctor_get(v___x_6032_, 1);
lean_inc(v_snd_6033_);
v_snd_6034_ = lean_ctor_get(v_snd_6033_, 1);
lean_inc(v_snd_6034_);
v_fst_6035_ = lean_ctor_get(v___x_6032_, 0);
lean_inc(v_fst_6035_);
lean_dec_ref(v___x_6032_);
v_fst_6036_ = lean_ctor_get(v_snd_6033_, 0);
v_isSharedCheck_6059_ = !lean_is_exclusive(v_snd_6033_);
if (v_isSharedCheck_6059_ == 0)
{
lean_object* v_unused_6060_; 
v_unused_6060_ = lean_ctor_get(v_snd_6033_, 1);
lean_dec(v_unused_6060_);
v___x_6038_ = v_snd_6033_;
v_isShared_6039_ = v_isSharedCheck_6059_;
goto v_resetjp_6037_;
}
else
{
lean_inc(v_fst_6036_);
lean_dec(v_snd_6033_);
v___x_6038_ = lean_box(0);
v_isShared_6039_ = v_isSharedCheck_6059_;
goto v_resetjp_6037_;
}
v_resetjp_6037_:
{
lean_object* v_fst_6040_; lean_object* v___x_6042_; uint8_t v_isShared_6043_; uint8_t v_isSharedCheck_6057_; 
v_fst_6040_ = lean_ctor_get(v_snd_6034_, 0);
v_isSharedCheck_6057_ = !lean_is_exclusive(v_snd_6034_);
if (v_isSharedCheck_6057_ == 0)
{
lean_object* v_unused_6058_; 
v_unused_6058_ = lean_ctor_get(v_snd_6034_, 1);
lean_dec(v_unused_6058_);
v___x_6042_ = v_snd_6034_;
v_isShared_6043_ = v_isSharedCheck_6057_;
goto v_resetjp_6041_;
}
else
{
lean_inc(v_fst_6040_);
lean_dec(v_snd_6034_);
v___x_6042_ = lean_box(0);
v_isShared_6043_ = v_isSharedCheck_6057_;
goto v_resetjp_6041_;
}
v_resetjp_6041_:
{
lean_object* v___x_6044_; size_t v_sz_6045_; size_t v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6049_; 
v___x_6044_ = lean_array_get_size(v_fst_6040_);
v_sz_6045_ = lean_array_size(v_perms_5990_);
v___x_6046_ = ((size_t)0ULL);
v___x_6047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6035_, v_sz_6045_, v___x_6046_, v_perms_5990_);
lean_dec(v_fst_6035_);
if (v_isShared_6018_ == 0)
{
lean_ctor_set(v___x_6017_, 1, v___x_6047_);
lean_ctor_set(v___x_6017_, 0, v___x_6044_);
v___x_6049_ = v___x_6017_;
goto v_reusejp_6048_;
}
else
{
lean_object* v_reuseFailAlloc_6056_; 
v_reuseFailAlloc_6056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6056_, 0, v___x_6044_);
lean_ctor_set(v_reuseFailAlloc_6056_, 1, v___x_6047_);
lean_ctor_set(v_reuseFailAlloc_6056_, 2, v_revDeps_5991_);
v___x_6049_ = v_reuseFailAlloc_6056_;
goto v_reusejp_6048_;
}
v_reusejp_6048_:
{
lean_object* v___x_6051_; 
if (v_isShared_6043_ == 0)
{
lean_ctor_set(v___x_6042_, 1, v_fst_6036_);
v___x_6051_ = v___x_6042_;
goto v_reusejp_6050_;
}
else
{
lean_object* v_reuseFailAlloc_6055_; 
v_reuseFailAlloc_6055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6055_, 0, v_fst_6040_);
lean_ctor_set(v_reuseFailAlloc_6055_, 1, v_fst_6036_);
v___x_6051_ = v_reuseFailAlloc_6055_;
goto v_reusejp_6050_;
}
v_reusejp_6050_:
{
lean_object* v___x_6053_; 
if (v_isShared_6039_ == 0)
{
lean_ctor_set(v___x_6038_, 1, v___x_6051_);
lean_ctor_set(v___x_6038_, 0, v___x_6049_);
v___x_6053_ = v___x_6038_;
goto v_reusejp_6052_;
}
else
{
lean_object* v_reuseFailAlloc_6054_; 
v_reuseFailAlloc_6054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6054_, 0, v___x_6049_);
lean_ctor_set(v_reuseFailAlloc_6054_, 1, v___x_6051_);
v___x_6053_ = v_reuseFailAlloc_6054_;
goto v_reusejp_6052_;
}
v_reusejp_6052_:
{
return v___x_6053_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6077_, lean_object* v___x_6078_, lean_object* v_fixedParamPerms_6079_, lean_object* v_next_6080_, lean_object* v_inst_6081_, lean_object* v_R_6082_, lean_object* v_a_6083_, lean_object* v_b_6084_, lean_object* v_c_6085_){
_start:
{
lean_object* v___x_6086_; 
v___x_6086_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6077_, v___x_6078_, v_fixedParamPerms_6079_, v_next_6080_, v_a_6083_, v_b_6084_);
return v___x_6086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6087_, lean_object* v___x_6088_, lean_object* v_fixedParamPerms_6089_, lean_object* v_next_6090_, lean_object* v_inst_6091_, lean_object* v_R_6092_, lean_object* v_a_6093_, lean_object* v_b_6094_, lean_object* v_c_6095_){
_start:
{
lean_object* v_res_6096_; 
v_res_6096_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6087_, v___x_6088_, v_fixedParamPerms_6089_, v_next_6090_, v_inst_6091_, v_R_6092_, v_a_6093_, v_b_6094_, v_c_6095_);
lean_dec(v_next_6090_);
lean_dec_ref(v_fixedParamPerms_6089_);
lean_dec_ref(v___x_6088_);
lean_dec(v_upperBound_6087_);
return v_res_6096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6097_, lean_object* v___x_6098_, lean_object* v_fixedParamPerms_6099_, lean_object* v_inst_6100_, lean_object* v_R_6101_, lean_object* v_a_6102_, lean_object* v_b_6103_, lean_object* v_c_6104_){
_start:
{
lean_object* v___x_6105_; 
v___x_6105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6097_, v___x_6098_, v_fixedParamPerms_6099_, v_a_6102_, v_b_6103_);
return v___x_6105_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6106_, lean_object* v___x_6107_, lean_object* v_fixedParamPerms_6108_, lean_object* v_inst_6109_, lean_object* v_R_6110_, lean_object* v_a_6111_, lean_object* v_b_6112_, lean_object* v_c_6113_){
_start:
{
lean_object* v_res_6114_; 
v_res_6114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6106_, v___x_6107_, v_fixedParamPerms_6108_, v_inst_6109_, v_R_6110_, v_a_6111_, v_b_6112_, v_c_6113_);
lean_dec_ref(v_fixedParamPerms_6108_);
lean_dec_ref(v___x_6107_);
lean_dec(v_upperBound_6106_);
return v_res_6114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6115_, lean_object* v_inst_6116_, lean_object* v_R_6117_, lean_object* v_a_6118_, lean_object* v_b_6119_, lean_object* v_c_6120_){
_start:
{
lean_object* v___x_6121_; 
v___x_6121_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6115_, v_a_6118_, v_b_6119_);
return v___x_6121_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6122_, lean_object* v_inst_6123_, lean_object* v_R_6124_, lean_object* v_a_6125_, lean_object* v_b_6126_, lean_object* v_c_6127_){
_start:
{
lean_object* v_res_6128_; 
v_res_6128_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6122_, v_inst_6123_, v_R_6124_, v_a_6125_, v_b_6126_, v_c_6127_);
lean_dec(v_upperBound_6122_);
return v_res_6128_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6129_, lean_object* v_inst_6130_, lean_object* v_R_6131_, lean_object* v_a_6132_, lean_object* v_b_6133_, lean_object* v_c_6134_){
_start:
{
lean_object* v___x_6135_; 
v___x_6135_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6129_, v_a_6132_, v_b_6133_);
return v___x_6135_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6136_, lean_object* v_inst_6137_, lean_object* v_R_6138_, lean_object* v_a_6139_, lean_object* v_b_6140_, lean_object* v_c_6141_){
_start:
{
lean_object* v_res_6142_; 
v_res_6142_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6136_, v_inst_6137_, v_R_6138_, v_a_6139_, v_b_6140_, v_c_6141_);
lean_dec(v_upperBound_6136_);
return v_res_6142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6200_; uint8_t v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; 
v___x_6200_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3));
v___x_6201_ = 0;
v___x_6202_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6203_ = l_Lean_registerTraceClass(v___x_6200_, v___x_6201_, v___x_6202_);
return v___x_6203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6204_){
_start:
{
lean_object* v_res_6205_; 
v_res_6205_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6205_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
