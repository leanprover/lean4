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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_1370_; lean_object* v_fileName_1379_; lean_object* v_fileMap_1380_; lean_object* v_options_1381_; lean_object* v_currRecDepth_1382_; lean_object* v_maxRecDepth_1383_; lean_object* v_ref_1384_; lean_object* v_currNamespace_1385_; lean_object* v_openDecls_1386_; lean_object* v_initHeartbeats_1387_; lean_object* v_maxHeartbeats_1388_; lean_object* v_quotContext_1389_; lean_object* v_currMacroScope_1390_; uint8_t v_diag_1391_; lean_object* v_cancelTk_x3f_1392_; uint8_t v_suppressElabErrors_1393_; lean_object* v_inheritedTraceOptions_1394_; uint8_t v___x_1395_; 
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
v___x_1395_ = lean_nat_dec_eq(v_currRecDepth_1382_, v_maxRecDepth_1383_);
if (v___x_1395_ == 0)
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
else
{
lean_object* v___x_1400_; 
lean_dec_ref(v_x_1362_);
lean_inc(v_ref_1384_);
v___x_1400_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg(v_ref_1384_);
v___y_1370_ = v___x_1400_;
goto v___jp_1369_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___redArg___boxed(lean_object* v_x_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___redArg(v_x_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___lam__0(lean_object* v_fvars_1411_, lean_object* v_pre_1412_, lean_object* v_post_1413_, uint8_t v_usedLetOnly_1414_, uint8_t v_skipConstInApp_1415_, uint8_t v_skipInstances_1416_, lean_object* v_body_1417_, lean_object* v_x_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_array_push(v_fvars_1411_, v_x_1418_);
v___x_1426_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14(v_pre_1412_, v_post_1413_, v_usedLetOnly_1414_, v_skipConstInApp_1415_, v_skipInstances_1416_, v___x_1425_, v_body_1417_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___lam__0___boxed(lean_object* v_fvars_1427_, lean_object* v_pre_1428_, lean_object* v_post_1429_, lean_object* v_usedLetOnly_1430_, lean_object* v_skipConstInApp_1431_, lean_object* v_skipInstances_1432_, lean_object* v_body_1433_, lean_object* v_x_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v_usedLetOnly_boxed_1441_; uint8_t v_skipConstInApp_boxed_1442_; uint8_t v_skipInstances_boxed_1443_; lean_object* v_res_1444_; 
v_usedLetOnly_boxed_1441_ = lean_unbox(v_usedLetOnly_1430_);
v_skipConstInApp_boxed_1442_ = lean_unbox(v_skipConstInApp_1431_);
v_skipInstances_boxed_1443_ = lean_unbox(v_skipInstances_1432_);
v_res_1444_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___lam__0(v_fvars_1427_, v_pre_1428_, v_post_1429_, v_usedLetOnly_boxed_1441_, v_skipConstInApp_boxed_1442_, v_skipInstances_boxed_1443_, v_body_1433_, v_x_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(lean_object* v_pre_1445_, lean_object* v_post_1446_, uint8_t v_usedLetOnly_1447_, uint8_t v_skipConstInApp_1448_, uint8_t v_skipInstances_1449_, lean_object* v_e_1450_, lean_object* v_a_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; 
lean_inc_ref(v_post_1446_);
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc_ref(v_e_1450_);
v___x_1457_ = lean_apply_6(v_post_1446_, v_e_1450_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, lean_box(0));
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1476_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1476_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1476_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
switch(lean_obj_tag(v_a_1458_))
{
case 0:
{
lean_object* v_e_1462_; lean_object* v___x_1464_; 
lean_dec_ref(v_e_1450_);
lean_dec_ref(v_post_1446_);
lean_dec_ref(v_pre_1445_);
v_e_1462_ = lean_ctor_get(v_a_1458_, 0);
lean_inc_ref(v_e_1462_);
lean_dec_ref(v_a_1458_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v_e_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_e_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
case 1:
{
lean_object* v_e_1466_; lean_object* v___x_1467_; 
lean_del_object(v___x_1460_);
lean_dec_ref(v_e_1450_);
v_e_1466_ = lean_ctor_get(v_a_1458_, 0);
lean_inc_ref(v_e_1466_);
lean_dec_ref(v_a_1458_);
v___x_1467_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1445_, v_post_1446_, v_usedLetOnly_1447_, v_skipConstInApp_1448_, v_skipInstances_1449_, v_e_1466_, v_a_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1467_;
}
default: 
{
lean_object* v_e_x3f_1468_; 
lean_dec_ref(v_post_1446_);
lean_dec_ref(v_pre_1445_);
v_e_x3f_1468_ = lean_ctor_get(v_a_1458_, 0);
lean_inc(v_e_x3f_1468_);
lean_dec_ref(v_a_1458_);
if (lean_obj_tag(v_e_x3f_1468_) == 0)
{
lean_object* v___x_1470_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v_e_1450_);
v___x_1470_ = v___x_1460_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_e_1450_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
else
{
lean_object* v_val_1472_; lean_object* v___x_1474_; 
lean_dec_ref(v_e_1450_);
v_val_1472_ = lean_ctor_get(v_e_x3f_1468_, 0);
lean_inc(v_val_1472_);
lean_dec_ref(v_e_x3f_1468_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v_val_1472_);
v___x_1474_ = v___x_1460_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_val_1472_);
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
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v_e_1450_);
lean_dec_ref(v_post_1446_);
lean_dec_ref(v_pre_1445_);
v_a_1477_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1457_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1457_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14(lean_object* v_pre_1485_, lean_object* v_post_1486_, uint8_t v_usedLetOnly_1487_, uint8_t v_skipConstInApp_1488_, uint8_t v_skipInstances_1489_, lean_object* v_fvars_1490_, lean_object* v_e_1491_, lean_object* v_a_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
if (lean_obj_tag(v_e_1491_) == 6)
{
lean_object* v_binderName_1498_; lean_object* v_binderType_1499_; lean_object* v_body_1500_; uint8_t v_binderInfo_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v_binderName_1498_ = lean_ctor_get(v_e_1491_, 0);
lean_inc(v_binderName_1498_);
v_binderType_1499_ = lean_ctor_get(v_e_1491_, 1);
lean_inc_ref(v_binderType_1499_);
v_body_1500_ = lean_ctor_get(v_e_1491_, 2);
lean_inc_ref(v_body_1500_);
v_binderInfo_1501_ = lean_ctor_get_uint8(v_e_1491_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1491_);
v___x_1502_ = lean_expr_instantiate_rev(v_binderType_1499_, v_fvars_1490_);
lean_dec_ref(v_binderType_1499_);
lean_inc_ref(v_post_1486_);
lean_inc_ref(v_pre_1485_);
v___x_1503_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1485_, v_post_1486_, v_usedLetOnly_1487_, v_skipConstInApp_1488_, v_skipInstances_1489_, v___x_1502_, v_a_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___f_1508_; uint8_t v___x_1509_; lean_object* v___x_1510_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref(v___x_1503_);
v___x_1505_ = lean_box(v_usedLetOnly_1487_);
v___x_1506_ = lean_box(v_skipConstInApp_1488_);
v___x_1507_ = lean_box(v_skipInstances_1489_);
v___f_1508_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1508_, 0, v_fvars_1490_);
lean_closure_set(v___f_1508_, 1, v_pre_1485_);
lean_closure_set(v___f_1508_, 2, v_post_1486_);
lean_closure_set(v___f_1508_, 3, v___x_1505_);
lean_closure_set(v___f_1508_, 4, v___x_1506_);
lean_closure_set(v___f_1508_, 5, v___x_1507_);
lean_closure_set(v___f_1508_, 6, v_body_1500_);
v___x_1509_ = 0;
v___x_1510_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg(v_binderName_1498_, v_binderInfo_1501_, v_a_1504_, v___f_1508_, v___x_1509_, v_a_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
return v___x_1510_;
}
else
{
lean_dec_ref(v_body_1500_);
lean_dec(v_binderName_1498_);
lean_dec_ref(v_fvars_1490_);
lean_dec_ref(v_post_1486_);
lean_dec_ref(v_pre_1485_);
return v___x_1503_;
}
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_expr_instantiate_rev(v_e_1491_, v_fvars_1490_);
lean_dec_ref(v_e_1491_);
lean_inc_ref(v_post_1486_);
lean_inc_ref(v_pre_1485_);
v___x_1512_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1485_, v_post_1486_, v_usedLetOnly_1487_, v_skipConstInApp_1488_, v_skipInstances_1489_, v___x_1511_, v_a_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; uint8_t v___x_1514_; uint8_t v___x_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref(v___x_1512_);
v___x_1514_ = 0;
v___x_1515_ = 1;
v___x_1516_ = 1;
v___x_1517_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1490_, v_a_1513_, v___x_1514_, v_usedLetOnly_1487_, v___x_1514_, v___x_1515_, v___x_1516_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec_ref(v_fvars_1490_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1485_, v_post_1486_, v_usedLetOnly_1487_, v_skipConstInApp_1488_, v_skipInstances_1489_, v_a_1518_, v_a_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
return v___x_1519_;
}
else
{
lean_dec_ref(v_post_1486_);
lean_dec_ref(v_pre_1485_);
return v___x_1517_;
}
}
else
{
lean_dec_ref(v_fvars_1490_);
lean_dec_ref(v_post_1486_);
lean_dec_ref(v_pre_1485_);
return v___x_1512_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___lam__0(lean_object* v_fvars_1520_, lean_object* v_pre_1521_, lean_object* v_post_1522_, uint8_t v_usedLetOnly_1523_, uint8_t v_skipConstInApp_1524_, uint8_t v_skipInstances_1525_, lean_object* v_body_1526_, lean_object* v_x_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_array_push(v_fvars_1520_, v_x_1527_);
v___x_1535_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15(v_pre_1521_, v_post_1522_, v_usedLetOnly_1523_, v_skipConstInApp_1524_, v_skipInstances_1525_, v___x_1534_, v_body_1526_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___lam__0___boxed(lean_object* v_fvars_1536_, lean_object* v_pre_1537_, lean_object* v_post_1538_, lean_object* v_usedLetOnly_1539_, lean_object* v_skipConstInApp_1540_, lean_object* v_skipInstances_1541_, lean_object* v_body_1542_, lean_object* v_x_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
uint8_t v_usedLetOnly_boxed_1550_; uint8_t v_skipConstInApp_boxed_1551_; uint8_t v_skipInstances_boxed_1552_; lean_object* v_res_1553_; 
v_usedLetOnly_boxed_1550_ = lean_unbox(v_usedLetOnly_1539_);
v_skipConstInApp_boxed_1551_ = lean_unbox(v_skipConstInApp_1540_);
v_skipInstances_boxed_1552_ = lean_unbox(v_skipInstances_1541_);
v_res_1553_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___lam__0(v_fvars_1536_, v_pre_1537_, v_post_1538_, v_usedLetOnly_boxed_1550_, v_skipConstInApp_boxed_1551_, v_skipInstances_boxed_1552_, v_body_1542_, v_x_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15(lean_object* v_pre_1554_, lean_object* v_post_1555_, uint8_t v_usedLetOnly_1556_, uint8_t v_skipConstInApp_1557_, uint8_t v_skipInstances_1558_, lean_object* v_fvars_1559_, lean_object* v_e_1560_, lean_object* v_a_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
if (lean_obj_tag(v_e_1560_) == 8)
{
lean_object* v_declName_1567_; lean_object* v_type_1568_; lean_object* v_value_1569_; lean_object* v_body_1570_; uint8_t v_nondep_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_declName_1567_ = lean_ctor_get(v_e_1560_, 0);
lean_inc(v_declName_1567_);
v_type_1568_ = lean_ctor_get(v_e_1560_, 1);
lean_inc_ref(v_type_1568_);
v_value_1569_ = lean_ctor_get(v_e_1560_, 2);
lean_inc_ref(v_value_1569_);
v_body_1570_ = lean_ctor_get(v_e_1560_, 3);
lean_inc_ref(v_body_1570_);
v_nondep_1571_ = lean_ctor_get_uint8(v_e_1560_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1560_);
v___x_1572_ = lean_expr_instantiate_rev(v_type_1568_, v_fvars_1559_);
lean_dec_ref(v_type_1568_);
lean_inc_ref(v_post_1555_);
lean_inc_ref(v_pre_1554_);
v___x_1573_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1554_, v_post_1555_, v_usedLetOnly_1556_, v_skipConstInApp_1557_, v_skipInstances_1558_, v___x_1572_, v_a_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref(v___x_1573_);
v___x_1575_ = lean_expr_instantiate_rev(v_value_1569_, v_fvars_1559_);
lean_dec_ref(v_value_1569_);
lean_inc_ref(v_post_1555_);
lean_inc_ref(v_pre_1554_);
v___x_1576_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1554_, v_post_1555_, v_usedLetOnly_1556_, v_skipConstInApp_1557_, v_skipInstances_1558_, v___x_1575_, v_a_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___f_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref(v___x_1576_);
v___x_1578_ = lean_box(v_usedLetOnly_1556_);
v___x_1579_ = lean_box(v_skipConstInApp_1557_);
v___x_1580_ = lean_box(v_skipInstances_1558_);
v___f_1581_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1581_, 0, v_fvars_1559_);
lean_closure_set(v___f_1581_, 1, v_pre_1554_);
lean_closure_set(v___f_1581_, 2, v_post_1555_);
lean_closure_set(v___f_1581_, 3, v___x_1578_);
lean_closure_set(v___f_1581_, 4, v___x_1579_);
lean_closure_set(v___f_1581_, 5, v___x_1580_);
lean_closure_set(v___f_1581_, 6, v_body_1570_);
v___x_1582_ = 0;
v___x_1583_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19___redArg(v_declName_1567_, v_a_1574_, v_a_1577_, v___f_1581_, v_nondep_1571_, v___x_1582_, v_a_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1583_;
}
else
{
lean_dec(v_a_1574_);
lean_dec_ref(v_body_1570_);
lean_dec(v_declName_1567_);
lean_dec_ref(v_fvars_1559_);
lean_dec_ref(v_post_1555_);
lean_dec_ref(v_pre_1554_);
return v___x_1576_;
}
}
else
{
lean_dec_ref(v_body_1570_);
lean_dec_ref(v_value_1569_);
lean_dec(v_declName_1567_);
lean_dec_ref(v_fvars_1559_);
lean_dec_ref(v_post_1555_);
lean_dec_ref(v_pre_1554_);
return v___x_1573_;
}
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_expr_instantiate_rev(v_e_1560_, v_fvars_1559_);
lean_dec_ref(v_e_1560_);
lean_inc_ref(v_post_1555_);
lean_inc_ref(v_pre_1554_);
v___x_1585_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1554_, v_post_1555_, v_usedLetOnly_1556_, v_skipConstInApp_1557_, v_skipInstances_1558_, v___x_1584_, v_a_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; uint8_t v___x_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v___x_1585_);
v___x_1587_ = 0;
v___x_1588_ = 1;
v___x_1589_ = l_Lean_Meta_mkLetFVars(v_fvars_1559_, v_a_1586_, v_usedLetOnly_1556_, v___x_1587_, v___x_1588_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec_ref(v_fvars_1559_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1554_, v_post_1555_, v_usedLetOnly_1556_, v_skipConstInApp_1557_, v_skipInstances_1558_, v_a_1590_, v_a_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1591_;
}
else
{
lean_dec_ref(v_post_1555_);
lean_dec_ref(v_pre_1554_);
return v___x_1589_;
}
}
else
{
lean_dec_ref(v_fvars_1559_);
lean_dec_ref(v_post_1555_);
lean_dec_ref(v_pre_1554_);
return v___x_1585_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1592_; lean_object* v_dummy_1593_; 
v___x_1592_ = lean_box(0);
v_dummy_1593_ = l_Lean_Expr_sort___override(v___x_1592_);
return v_dummy_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__9(lean_object* v_pre_1594_, lean_object* v_post_1595_, uint8_t v_usedLetOnly_1596_, uint8_t v_skipConstInApp_1597_, uint8_t v_skipInstances_1598_, size_t v_sz_1599_, size_t v_i_1600_, lean_object* v_bs_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_usize_dec_lt(v_i_1600_, v_sz_1599_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref(v_post_1595_);
lean_dec_ref(v_pre_1594_);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_bs_1601_);
return v___x_1609_;
}
else
{
lean_object* v_v_1610_; lean_object* v___x_1611_; 
v_v_1610_ = lean_array_uget_borrowed(v_bs_1601_, v_i_1600_);
lean_inc(v_v_1610_);
lean_inc_ref(v_post_1595_);
lean_inc_ref(v_pre_1594_);
v___x_1611_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1594_, v_post_1595_, v_usedLetOnly_1596_, v_skipConstInApp_1597_, v_skipInstances_1598_, v_v_1610_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; lean_object* v_bs_x27_1614_; size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref(v___x_1611_);
v___x_1613_ = lean_unsigned_to_nat(0u);
v_bs_x27_1614_ = lean_array_uset(v_bs_1601_, v_i_1600_, v___x_1613_);
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_i_1600_, v___x_1615_);
v___x_1617_ = lean_array_uset(v_bs_x27_1614_, v_i_1600_, v_a_1612_);
v_i_1600_ = v___x_1616_;
v_bs_1601_ = v___x_1617_;
goto _start;
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v_bs_1601_);
lean_dec_ref(v_post_1595_);
lean_dec_ref(v_pre_1594_);
v_a_1619_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1611_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1611_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__0(lean_object* v_pre_1627_, lean_object* v_post_1628_, uint8_t v_usedLetOnly_1629_, uint8_t v_skipConstInApp_1630_, uint8_t v_skipInstances_1631_, lean_object* v___x_1632_, lean_object* v___y_1633_, lean_object* v_b_1634_, lean_object* v_a_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1627_, v_post_1628_, v_usedLetOnly_1629_, v_skipConstInApp_1630_, v_skipInstances_1631_, v___x_1632_, v___y_1633_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1651_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1651_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1651_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1646_ = lean_array_fset(v_b_1634_, v_a_1635_, v_a_1642_);
v___x_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1647_);
v___x_1649_ = v___x_1644_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v_b_1634_);
v_a_1652_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1641_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1641_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__0___boxed(lean_object* v_pre_1660_, lean_object* v_post_1661_, lean_object* v_usedLetOnly_1662_, lean_object* v_skipConstInApp_1663_, lean_object* v_skipInstances_1664_, lean_object* v___x_1665_, lean_object* v___y_1666_, lean_object* v_b_1667_, lean_object* v_a_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
uint8_t v_usedLetOnly_boxed_1674_; uint8_t v_skipConstInApp_boxed_1675_; uint8_t v_skipInstances_boxed_1676_; lean_object* v_res_1677_; 
v_usedLetOnly_boxed_1674_ = lean_unbox(v_usedLetOnly_1662_);
v_skipConstInApp_boxed_1675_ = lean_unbox(v_skipConstInApp_1663_);
v_skipInstances_boxed_1676_ = lean_unbox(v_skipInstances_1664_);
v_res_1677_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__0(v_pre_1660_, v_post_1661_, v_usedLetOnly_boxed_1674_, v_skipConstInApp_boxed_1675_, v_skipInstances_boxed_1676_, v___x_1665_, v___y_1666_, v_b_1667_, v_a_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v_a_1668_);
lean_dec(v___y_1666_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg(lean_object* v_upperBound_1678_, lean_object* v___x_1679_, lean_object* v_pre_1680_, lean_object* v_post_1681_, uint8_t v_usedLetOnly_1682_, uint8_t v_skipConstInApp_1683_, uint8_t v_skipInstances_1684_, lean_object* v_a_1685_, lean_object* v_b_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___y_1694_; uint8_t v___x_1717_; 
v___x_1717_ = lean_nat_dec_lt(v_a_1685_, v_upperBound_1678_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
lean_dec(v_a_1685_);
lean_dec_ref(v_post_1681_);
lean_dec_ref(v_pre_1680_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_b_1686_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1719_ = lean_array_fget_borrowed(v_b_1686_, v_a_1685_);
v___x_1720_ = lean_array_get_size(v___x_1679_);
v___x_1721_ = lean_nat_dec_lt(v_a_1685_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___f_1725_; 
lean_inc(v___x_1719_);
v___x_1722_ = lean_box(v_usedLetOnly_1682_);
v___x_1723_ = lean_box(v_skipConstInApp_1683_);
v___x_1724_ = lean_box(v_skipInstances_1684_);
lean_inc(v_a_1685_);
lean_inc(v___y_1687_);
lean_inc_ref(v_post_1681_);
lean_inc_ref(v_pre_1680_);
v___f_1725_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1725_, 0, v_pre_1680_);
lean_closure_set(v___f_1725_, 1, v_post_1681_);
lean_closure_set(v___f_1725_, 2, v___x_1722_);
lean_closure_set(v___f_1725_, 3, v___x_1723_);
lean_closure_set(v___f_1725_, 4, v___x_1724_);
lean_closure_set(v___f_1725_, 5, v___x_1719_);
lean_closure_set(v___f_1725_, 6, v___y_1687_);
lean_closure_set(v___f_1725_, 7, v_b_1686_);
lean_closure_set(v___f_1725_, 8, v_a_1685_);
v___y_1694_ = v___f_1725_;
goto v___jp_1693_;
}
else
{
lean_object* v___x_1726_; uint8_t v_isInstance_1727_; 
v___x_1726_ = lean_array_fget_borrowed(v___x_1679_, v_a_1685_);
v_isInstance_1727_ = lean_ctor_get_uint8(v___x_1726_, sizeof(void*)*1 + 4);
if (v_isInstance_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___f_1731_; 
lean_inc(v___x_1719_);
v___x_1728_ = lean_box(v_usedLetOnly_1682_);
v___x_1729_ = lean_box(v_skipConstInApp_1683_);
v___x_1730_ = lean_box(v_skipInstances_1684_);
lean_inc(v_a_1685_);
lean_inc(v___y_1687_);
lean_inc_ref(v_post_1681_);
lean_inc_ref(v_pre_1680_);
v___f_1731_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1731_, 0, v_pre_1680_);
lean_closure_set(v___f_1731_, 1, v_post_1681_);
lean_closure_set(v___f_1731_, 2, v___x_1728_);
lean_closure_set(v___f_1731_, 3, v___x_1729_);
lean_closure_set(v___f_1731_, 4, v___x_1730_);
lean_closure_set(v___f_1731_, 5, v___x_1719_);
lean_closure_set(v___f_1731_, 6, v___y_1687_);
lean_closure_set(v___f_1731_, 7, v_b_1686_);
lean_closure_set(v___f_1731_, 8, v_a_1685_);
v___y_1694_ = v___f_1731_;
goto v___jp_1693_;
}
else
{
lean_object* v___x_1732_; lean_object* v___f_1733_; 
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_b_1686_);
v___f_1733_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1733_, 0, v___x_1732_);
v___y_1694_ = v___f_1733_;
goto v___jp_1693_;
}
}
}
v___jp_1693_:
{
lean_object* v___x_1695_; 
lean_inc(v___y_1691_);
lean_inc_ref(v___y_1690_);
lean_inc(v___y_1689_);
lean_inc_ref(v___y_1688_);
v___x_1695_ = lean_apply_5(v___y_1694_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, lean_box(0));
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1708_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1708_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1708_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
if (lean_obj_tag(v_a_1696_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; 
lean_dec(v_a_1685_);
lean_dec_ref(v_post_1681_);
lean_dec_ref(v_pre_1680_);
v_a_1700_ = lean_ctor_get(v_a_1696_, 0);
lean_inc(v_a_1700_);
lean_dec_ref(v_a_1696_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v_a_1700_);
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_del_object(v___x_1698_);
v_a_1704_ = lean_ctor_get(v_a_1696_, 0);
lean_inc(v_a_1704_);
lean_dec_ref(v_a_1696_);
v___x_1705_ = lean_unsigned_to_nat(1u);
v___x_1706_ = lean_nat_add(v_a_1685_, v___x_1705_);
lean_dec(v_a_1685_);
v_a_1685_ = v___x_1706_;
v_b_1686_ = v_a_1704_;
goto _start;
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_a_1685_);
lean_dec_ref(v_post_1681_);
lean_dec_ref(v_pre_1680_);
v_a_1709_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1695_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1695_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__16(uint8_t v_skipInstances_1734_, lean_object* v_pre_1735_, lean_object* v_post_1736_, uint8_t v_usedLetOnly_1737_, uint8_t v_skipConstInApp_1738_, lean_object* v_x_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_f_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; 
if (lean_obj_tag(v_x_1739_) == 5)
{
lean_object* v_fn_1797_; lean_object* v_arg_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_fn_1797_ = lean_ctor_get(v_x_1739_, 0);
lean_inc_ref(v_fn_1797_);
v_arg_1798_ = lean_ctor_get(v_x_1739_, 1);
lean_inc_ref(v_arg_1798_);
lean_dec_ref(v_x_1739_);
v___x_1799_ = lean_array_set(v_x_1740_, v_x_1741_, v_arg_1798_);
v___x_1800_ = lean_unsigned_to_nat(1u);
v___x_1801_ = lean_nat_sub(v_x_1741_, v___x_1800_);
lean_dec(v_x_1741_);
v_x_1739_ = v_fn_1797_;
v_x_1740_ = v___x_1799_;
v_x_1741_ = v___x_1801_;
goto _start;
}
else
{
lean_dec(v_x_1741_);
if (v_skipConstInApp_1738_ == 0)
{
goto v___jp_1794_;
}
else
{
uint8_t v___x_1803_; 
v___x_1803_ = l_Lean_Expr_isConst(v_x_1739_);
if (v___x_1803_ == 0)
{
goto v___jp_1794_;
}
else
{
v_f_1749_ = v_x_1739_;
v___y_1750_ = v___y_1742_;
v___y_1751_ = v___y_1743_;
v___y_1752_ = v___y_1744_;
v___y_1753_ = v___y_1745_;
v___y_1754_ = v___y_1746_;
goto v___jp_1748_;
}
}
}
v___jp_1748_:
{
if (v_skipInstances_1734_ == 0)
{
size_t v_sz_1755_; size_t v___x_1756_; lean_object* v___x_1757_; 
v_sz_1755_ = lean_array_size(v_x_1740_);
v___x_1756_ = ((size_t)0ULL);
lean_inc_ref(v_post_1736_);
lean_inc_ref(v_pre_1735_);
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__9(v_pre_1735_, v_post_1736_, v_usedLetOnly_1737_, v_skipConstInApp_1738_, v_skipInstances_1734_, v_sz_1755_, v___x_1756_, v_x_1740_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = l_Lean_mkAppN(v_f_1749_, v_a_1758_);
lean_dec(v_a_1758_);
v___x_1760_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1735_, v_post_1736_, v_usedLetOnly_1737_, v_skipConstInApp_1738_, v_skipInstances_1734_, v___x_1759_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1760_;
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref(v_f_1749_);
lean_dec_ref(v_post_1736_);
lean_dec_ref(v_pre_1735_);
v_a_1761_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1757_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1757_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = lean_array_get_size(v_x_1740_);
lean_inc_ref(v_f_1749_);
v___x_1770_ = l_Lean_Meta_getFunInfoNArgs(v_f_1749_, v___x_1769_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v_paramInfo_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
v_paramInfo_1772_ = lean_ctor_get(v_a_1771_, 0);
lean_inc_ref(v_paramInfo_1772_);
lean_dec(v_a_1771_);
v___x_1773_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1736_);
lean_inc_ref(v_pre_1735_);
v___x_1774_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg(v___x_1769_, v_paramInfo_1772_, v_pre_1735_, v_post_1736_, v_usedLetOnly_1737_, v_skipConstInApp_1738_, v_skipInstances_1734_, v___x_1773_, v_x_1740_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec_ref(v_paramInfo_1772_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___x_1774_);
v___x_1776_ = l_Lean_mkAppN(v_f_1749_, v_a_1775_);
lean_dec(v_a_1775_);
v___x_1777_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1735_, v_post_1736_, v_usedLetOnly_1737_, v_skipConstInApp_1738_, v_skipInstances_1734_, v___x_1776_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1777_;
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec_ref(v_f_1749_);
lean_dec_ref(v_post_1736_);
lean_dec_ref(v_pre_1735_);
v_a_1778_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1774_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1774_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v_f_1749_);
lean_dec_ref(v_x_1740_);
lean_dec_ref(v_post_1736_);
lean_dec_ref(v_pre_1735_);
v_a_1786_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1770_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1770_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
v___jp_1794_:
{
lean_object* v___x_1795_; 
lean_inc_ref(v_post_1736_);
lean_inc_ref(v_pre_1735_);
v___x_1795_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1735_, v_post_1736_, v_usedLetOnly_1737_, v_skipConstInApp_1738_, v_skipInstances_1734_, v_x_1739_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref(v___x_1795_);
v_f_1749_ = v_a_1796_;
v___y_1750_ = v___y_1742_;
v___y_1751_ = v___y_1743_;
v___y_1752_ = v___y_1744_;
v___y_1753_ = v___y_1745_;
v___y_1754_ = v___y_1746_;
goto v___jp_1748_;
}
else
{
lean_dec_ref(v_x_1740_);
lean_dec_ref(v_post_1736_);
lean_dec_ref(v_pre_1735_);
return v___x_1795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1(lean_object* v_pre_1804_, lean_object* v_e_1805_, lean_object* v_post_1806_, uint8_t v_usedLetOnly_1807_, uint8_t v_skipConstInApp_1808_, uint8_t v_skipInstances_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
lean_inc_ref(v_pre_1804_);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
lean_inc_ref(v_e_1805_);
v___x_1816_ = lean_apply_6(v_pre_1804_, v_e_1805_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, lean_box(0));
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1865_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1865_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1865_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___y_1822_; 
switch(lean_obj_tag(v_a_1817_))
{
case 0:
{
lean_object* v_e_1857_; lean_object* v___x_1859_; 
lean_dec_ref(v_post_1806_);
lean_dec_ref(v_e_1805_);
lean_dec_ref(v_pre_1804_);
v_e_1857_ = lean_ctor_get(v_a_1817_, 0);
lean_inc_ref(v_e_1857_);
lean_dec_ref(v_a_1817_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v_e_1857_);
v___x_1859_ = v___x_1819_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_e_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
case 1:
{
lean_object* v_e_1861_; lean_object* v___x_1862_; 
lean_del_object(v___x_1819_);
lean_dec_ref(v_e_1805_);
v_e_1861_ = lean_ctor_get(v_a_1817_, 0);
lean_inc_ref(v_e_1861_);
lean_dec_ref(v_a_1817_);
v___x_1862_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1804_, v_post_1806_, v_usedLetOnly_1807_, v_skipConstInApp_1808_, v_skipInstances_1809_, v_e_1861_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1862_;
}
default: 
{
lean_object* v_e_x3f_1863_; 
lean_del_object(v___x_1819_);
v_e_x3f_1863_ = lean_ctor_get(v_a_1817_, 0);
lean_inc(v_e_x3f_1863_);
lean_dec_ref(v_a_1817_);
if (lean_obj_tag(v_e_x3f_1863_) == 0)
{
v___y_1822_ = v_e_1805_;
goto v___jp_1821_;
}
else
{
lean_object* v_val_1864_; 
lean_dec_ref(v_e_1805_);
v_val_1864_ = lean_ctor_get(v_e_x3f_1863_, 0);
lean_inc(v_val_1864_);
lean_dec_ref(v_e_x3f_1863_);
v___y_1822_ = v_val_1864_;
goto v___jp_1821_;
}
}
}
v___jp_1821_:
{
switch(lean_obj_tag(v___y_1822_))
{
case 7:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__0));
v___x_1824_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13(v_pre_1804_, v_post_1806_, v_usedLetOnly_1807_, v_skipConstInApp_1808_, v_skipInstances_1809_, v___x_1823_, v___y_1822_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1824_;
}
case 6:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__0));
v___x_1826_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14(v_pre_1804_, v_post_1806_, v_usedLetOnly_1807_, v_skipConstInApp_1808_, v_skipInstances_1809_, v___x_1825_, v___y_1822_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1826_;
}
case 8:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__0));
v___x_1828_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15(v_pre_1804_, v_post_1806_, v_usedLetOnly_1807_, v_skipConstInApp_1808_, v_skipInstances_1809_, v___x_1827_, v___y_1822_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1828_;
}
case 5:
{
lean_object* v_dummy_1829_; lean_object* v_nargs_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_dummy_1829_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1);
v_nargs_1830_ = l_Lean_Expr_getAppNumArgs(v___y_1822_);
lean_inc(v_nargs_1830_);
v___x_1831_ = lean_mk_array(v_nargs_1830_, v_dummy_1829_);
v___x_1832_ = lean_unsigned_to_nat(1u);
v___x_1833_ = lean_nat_sub(v_nargs_1830_, v___x_1832_);
lean_dec(v_nargs_1830_);
v___x_1834_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__16(v_skipInstances_1809_, v_pre_1804_, v_post_1806_, v_usedLetOnly_1807_, v_skipConstInApp_1808_, v___y_1822_, v___x_1831_, v___x_1833_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1834_;
}
case 10:
{
lean_object* v_data_1835_; lean_object* v_expr_1836_; lean_object* v___x_1837_; 
v_data_1835_ = lean_ctor_get(v___y_1822_, 0);
v_expr_1836_ = lean_ctor_get(v___y_1822_, 1);
lean_inc_ref(v_expr_1836_);
lean_inc_ref(v_post_1806_);
lean_inc_ref(v_pre_1804_);
v___x_1837_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1804_, v_post_1806_, v_usedLetOnly_1807_, v_skipConstInApp_1808_, v_skipInstances_1809_, v_expr_1836_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; size_t v___x_1839_; size_t v___x_1840_; uint8_t v___x_1841_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = lean_ptr_addr(v_expr_1836_);
v___x_1840_ = lean_ptr_addr(v_a_1838_);
v___x_1841_ = lean_usize_dec_eq(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
lean_inc(v_data_1835_);
lean_dec_ref(v___y_1822_);
v___x_1842_ = l_Lean_Expr_mdata___override(v_data_1835_, v_a_1838_);
v___x_1843_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1804_, v_post_1806_, v_usedLetOnly_1807_, v_skipConstInApp_1808_, v_skipInstances_1809_, v___x_1842_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1843_;
}
else
{
lean_object* v___x_1844_; 
lean_dec(v_a_1838_);
v___x_1844_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1804_, v_post_1806_, v_usedLetOnly_1807_, v_skipConstInApp_1808_, v_skipInstances_1809_, v___y_1822_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1844_;
}
}
else
{
lean_dec_ref(v___y_1822_);
lean_dec_ref(v_post_1806_);
lean_dec_ref(v_pre_1804_);
return v___x_1837_;
}
}
case 11:
{
lean_object* v_typeName_1845_; lean_object* v_idx_1846_; lean_object* v_struct_1847_; lean_object* v___x_1848_; 
v_typeName_1845_ = lean_ctor_get(v___y_1822_, 0);
v_idx_1846_ = lean_ctor_get(v___y_1822_, 1);
v_struct_1847_ = lean_ctor_get(v___y_1822_, 2);
lean_inc_ref(v_struct_1847_);
lean_inc_ref(v_post_1806_);
lean_inc_ref(v_pre_1804_);
v___x_1848_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1804_, v_post_1806_, v_usedLetOnly_1807_, v_skipConstInApp_1808_, v_skipInstances_1809_, v_struct_1847_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; size_t v___x_1850_; size_t v___x_1851_; uint8_t v___x_1852_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = lean_ptr_addr(v_struct_1847_);
v___x_1851_ = lean_ptr_addr(v_a_1849_);
v___x_1852_ = lean_usize_dec_eq(v___x_1850_, v___x_1851_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_inc(v_idx_1846_);
lean_inc(v_typeName_1845_);
lean_dec_ref(v___y_1822_);
v___x_1853_ = l_Lean_Expr_proj___override(v_typeName_1845_, v_idx_1846_, v_a_1849_);
v___x_1854_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1804_, v_post_1806_, v_usedLetOnly_1807_, v_skipConstInApp_1808_, v_skipInstances_1809_, v___x_1853_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; 
lean_dec(v_a_1849_);
v___x_1855_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1804_, v_post_1806_, v_usedLetOnly_1807_, v_skipConstInApp_1808_, v_skipInstances_1809_, v___y_1822_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1855_;
}
}
else
{
lean_dec_ref(v___y_1822_);
lean_dec_ref(v_post_1806_);
lean_dec_ref(v_pre_1804_);
return v___x_1848_;
}
}
default: 
{
lean_object* v___x_1856_; 
v___x_1856_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1804_, v_post_1806_, v_usedLetOnly_1807_, v_skipConstInApp_1808_, v_skipInstances_1809_, v___y_1822_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1856_;
}
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec_ref(v_post_1806_);
lean_dec_ref(v_e_1805_);
lean_dec_ref(v_pre_1804_);
v_a_1866_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1816_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1816_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___boxed(lean_object* v_pre_1874_, lean_object* v_e_1875_, lean_object* v_post_1876_, lean_object* v_usedLetOnly_1877_, lean_object* v_skipConstInApp_1878_, lean_object* v_skipInstances_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
uint8_t v_usedLetOnly_boxed_1886_; uint8_t v_skipConstInApp_boxed_1887_; uint8_t v_skipInstances_boxed_1888_; lean_object* v_res_1889_; 
v_usedLetOnly_boxed_1886_ = lean_unbox(v_usedLetOnly_1877_);
v_skipConstInApp_boxed_1887_ = lean_unbox(v_skipConstInApp_1878_);
v_skipInstances_boxed_1888_ = lean_unbox(v_skipInstances_1879_);
v_res_1889_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1(v_pre_1874_, v_e_1875_, v_post_1876_, v_usedLetOnly_boxed_1886_, v_skipConstInApp_boxed_1887_, v_skipInstances_boxed_1888_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(lean_object* v_pre_1890_, lean_object* v_post_1891_, uint8_t v_usedLetOnly_1892_, uint8_t v_skipConstInApp_1893_, uint8_t v_skipInstances_1894_, lean_object* v_e_1895_, lean_object* v_a_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_inc(v_a_1896_);
v___x_1902_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1902_, 0, lean_box(0));
lean_closure_set(v___x_1902_, 1, lean_box(0));
lean_closure_set(v___x_1902_, 2, v_a_1896_);
v___x_1903_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__0(lean_box(0), v___x_1902_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1937_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1906_ = v___x_1903_;
v_isShared_1907_ = v_isSharedCheck_1937_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1937_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12___redArg(v_a_1904_, v_e_1895_);
lean_dec(v_a_1904_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___f_1912_; lean_object* v___x_1913_; 
lean_del_object(v___x_1906_);
v___x_1909_ = lean_box(v_usedLetOnly_1892_);
v___x_1910_ = lean_box(v_skipConstInApp_1893_);
v___x_1911_ = lean_box(v_skipInstances_1894_);
lean_inc_ref(v_e_1895_);
v___f_1912_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1912_, 0, v_pre_1890_);
lean_closure_set(v___f_1912_, 1, v_e_1895_);
lean_closure_set(v___f_1912_, 2, v_post_1891_);
lean_closure_set(v___f_1912_, 3, v___x_1909_);
lean_closure_set(v___f_1912_, 4, v___x_1910_);
lean_closure_set(v___f_1912_, 5, v___x_1911_);
v___x_1913_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___redArg(v___f_1912_, v_a_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___f_1915_; lean_object* v___x_1916_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc_n(v_a_1914_, 2);
lean_dec_ref(v___x_1913_);
lean_inc(v_a_1896_);
v___f_1915_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1915_, 0, v_a_1896_);
lean_closure_set(v___f_1915_, 1, v_e_1895_);
lean_closure_set(v___f_1915_, 2, v_a_1914_);
v___x_1916_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__0(lean_box(0), v___f_1915_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; 
v_unused_1924_ = lean_ctor_get(v___x_1916_, 0);
lean_dec(v_unused_1924_);
v___x_1918_ = v___x_1916_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_dec(v___x_1916_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v_a_1914_);
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1914_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v_a_1914_);
v_a_1925_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1916_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1916_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_dec_ref(v_e_1895_);
return v___x_1913_;
}
}
else
{
lean_object* v_val_1933_; lean_object* v___x_1935_; 
lean_dec_ref(v_e_1895_);
lean_dec_ref(v_post_1891_);
lean_dec_ref(v_pre_1890_);
v_val_1933_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_val_1933_);
lean_dec_ref(v___x_1908_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v_val_1933_);
v___x_1935_ = v___x_1906_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_val_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v_e_1895_);
lean_dec_ref(v_post_1891_);
lean_dec_ref(v_pre_1890_);
v_a_1938_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1903_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1903_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___lam__0___boxed(lean_object* v_fvars_1946_, lean_object* v_pre_1947_, lean_object* v_post_1948_, lean_object* v_usedLetOnly_1949_, lean_object* v_skipConstInApp_1950_, lean_object* v_skipInstances_1951_, lean_object* v_body_1952_, lean_object* v_x_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
uint8_t v_usedLetOnly_boxed_1960_; uint8_t v_skipConstInApp_boxed_1961_; uint8_t v_skipInstances_boxed_1962_; lean_object* v_res_1963_; 
v_usedLetOnly_boxed_1960_ = lean_unbox(v_usedLetOnly_1949_);
v_skipConstInApp_boxed_1961_ = lean_unbox(v_skipConstInApp_1950_);
v_skipInstances_boxed_1962_ = lean_unbox(v_skipInstances_1951_);
v_res_1963_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___lam__0(v_fvars_1946_, v_pre_1947_, v_post_1948_, v_usedLetOnly_boxed_1960_, v_skipConstInApp_boxed_1961_, v_skipInstances_boxed_1962_, v_body_1952_, v_x_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13(lean_object* v_pre_1964_, lean_object* v_post_1965_, uint8_t v_usedLetOnly_1966_, uint8_t v_skipConstInApp_1967_, uint8_t v_skipInstances_1968_, lean_object* v_fvars_1969_, lean_object* v_e_1970_, lean_object* v_a_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
if (lean_obj_tag(v_e_1970_) == 7)
{
lean_object* v_binderName_1977_; lean_object* v_binderType_1978_; lean_object* v_body_1979_; uint8_t v_binderInfo_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_binderName_1977_ = lean_ctor_get(v_e_1970_, 0);
lean_inc(v_binderName_1977_);
v_binderType_1978_ = lean_ctor_get(v_e_1970_, 1);
lean_inc_ref(v_binderType_1978_);
v_body_1979_ = lean_ctor_get(v_e_1970_, 2);
lean_inc_ref(v_body_1979_);
v_binderInfo_1980_ = lean_ctor_get_uint8(v_e_1970_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1970_);
v___x_1981_ = lean_expr_instantiate_rev(v_binderType_1978_, v_fvars_1969_);
lean_dec_ref(v_binderType_1978_);
lean_inc_ref(v_post_1965_);
lean_inc_ref(v_pre_1964_);
v___x_1982_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1964_, v_post_1965_, v_usedLetOnly_1966_, v_skipConstInApp_1967_, v_skipInstances_1968_, v___x_1981_, v_a_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___f_1987_; uint8_t v___x_1988_; lean_object* v___x_1989_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref(v___x_1982_);
v___x_1984_ = lean_box(v_usedLetOnly_1966_);
v___x_1985_ = lean_box(v_skipConstInApp_1967_);
v___x_1986_ = lean_box(v_skipInstances_1968_);
v___f_1987_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1987_, 0, v_fvars_1969_);
lean_closure_set(v___f_1987_, 1, v_pre_1964_);
lean_closure_set(v___f_1987_, 2, v_post_1965_);
lean_closure_set(v___f_1987_, 3, v___x_1984_);
lean_closure_set(v___f_1987_, 4, v___x_1985_);
lean_closure_set(v___f_1987_, 5, v___x_1986_);
lean_closure_set(v___f_1987_, 6, v_body_1979_);
v___x_1988_ = 0;
v___x_1989_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg(v_binderName_1977_, v_binderInfo_1980_, v_a_1983_, v___f_1987_, v___x_1988_, v_a_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
return v___x_1989_;
}
else
{
lean_dec_ref(v_body_1979_);
lean_dec(v_binderName_1977_);
lean_dec_ref(v_fvars_1969_);
lean_dec_ref(v_post_1965_);
lean_dec_ref(v_pre_1964_);
return v___x_1982_;
}
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = lean_expr_instantiate_rev(v_e_1970_, v_fvars_1969_);
lean_dec_ref(v_e_1970_);
lean_inc_ref(v_post_1965_);
lean_inc_ref(v_pre_1964_);
v___x_1991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_1964_, v_post_1965_, v_usedLetOnly_1966_, v_skipConstInApp_1967_, v_skipInstances_1968_, v___x_1990_, v_a_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; uint8_t v___x_1993_; uint8_t v___x_1994_; uint8_t v___x_1995_; lean_object* v___x_1996_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref(v___x_1991_);
v___x_1993_ = 0;
v___x_1994_ = 1;
v___x_1995_ = 1;
v___x_1996_ = l_Lean_Meta_mkForallFVars(v_fvars_1969_, v_a_1992_, v___x_1993_, v_usedLetOnly_1966_, v___x_1994_, v___x_1995_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec_ref(v_fvars_1969_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref(v___x_1996_);
v___x_1998_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_1964_, v_post_1965_, v_usedLetOnly_1966_, v_skipConstInApp_1967_, v_skipInstances_1968_, v_a_1997_, v_a_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
return v___x_1998_;
}
else
{
lean_dec_ref(v_post_1965_);
lean_dec_ref(v_pre_1964_);
return v___x_1996_;
}
}
else
{
lean_dec_ref(v_fvars_1969_);
lean_dec_ref(v_post_1965_);
lean_dec_ref(v_pre_1964_);
return v___x_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___lam__0(lean_object* v_fvars_1999_, lean_object* v_pre_2000_, lean_object* v_post_2001_, uint8_t v_usedLetOnly_2002_, uint8_t v_skipConstInApp_2003_, uint8_t v_skipInstances_2004_, lean_object* v_body_2005_, lean_object* v_x_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_array_push(v_fvars_1999_, v_x_2006_);
v___x_2014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13(v_pre_2000_, v_post_2001_, v_usedLetOnly_2002_, v_skipConstInApp_2003_, v_skipInstances_2004_, v___x_2013_, v_body_2005_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10___boxed(lean_object* v_pre_2015_, lean_object* v_post_2016_, lean_object* v_usedLetOnly_2017_, lean_object* v_skipConstInApp_2018_, lean_object* v_skipInstances_2019_, lean_object* v_e_2020_, lean_object* v_a_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
uint8_t v_usedLetOnly_boxed_2027_; uint8_t v_skipConstInApp_boxed_2028_; uint8_t v_skipInstances_boxed_2029_; lean_object* v_res_2030_; 
v_usedLetOnly_boxed_2027_ = lean_unbox(v_usedLetOnly_2017_);
v_skipConstInApp_boxed_2028_ = lean_unbox(v_skipConstInApp_2018_);
v_skipInstances_boxed_2029_ = lean_unbox(v_skipInstances_2019_);
v_res_2030_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__10(v_pre_2015_, v_post_2016_, v_usedLetOnly_boxed_2027_, v_skipConstInApp_boxed_2028_, v_skipInstances_boxed_2029_, v_e_2020_, v_a_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v_a_2021_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__9___boxed(lean_object* v_pre_2031_, lean_object* v_post_2032_, lean_object* v_usedLetOnly_2033_, lean_object* v_skipConstInApp_2034_, lean_object* v_skipInstances_2035_, lean_object* v_sz_2036_, lean_object* v_i_2037_, lean_object* v_bs_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
uint8_t v_usedLetOnly_boxed_2045_; uint8_t v_skipConstInApp_boxed_2046_; uint8_t v_skipInstances_boxed_2047_; size_t v_sz_boxed_2048_; size_t v_i_boxed_2049_; lean_object* v_res_2050_; 
v_usedLetOnly_boxed_2045_ = lean_unbox(v_usedLetOnly_2033_);
v_skipConstInApp_boxed_2046_ = lean_unbox(v_skipConstInApp_2034_);
v_skipInstances_boxed_2047_ = lean_unbox(v_skipInstances_2035_);
v_sz_boxed_2048_ = lean_unbox_usize(v_sz_2036_);
lean_dec(v_sz_2036_);
v_i_boxed_2049_ = lean_unbox_usize(v_i_2037_);
lean_dec(v_i_2037_);
v_res_2050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__9(v_pre_2031_, v_post_2032_, v_usedLetOnly_boxed_2045_, v_skipConstInApp_boxed_2046_, v_skipInstances_boxed_2047_, v_sz_boxed_2048_, v_i_boxed_2049_, v_bs_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___boxed(lean_object* v_pre_2051_, lean_object* v_post_2052_, lean_object* v_usedLetOnly_2053_, lean_object* v_skipConstInApp_2054_, lean_object* v_skipInstances_2055_, lean_object* v_e_2056_, lean_object* v_a_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
uint8_t v_usedLetOnly_boxed_2063_; uint8_t v_skipConstInApp_boxed_2064_; uint8_t v_skipInstances_boxed_2065_; lean_object* v_res_2066_; 
v_usedLetOnly_boxed_2063_ = lean_unbox(v_usedLetOnly_2053_);
v_skipConstInApp_boxed_2064_ = lean_unbox(v_skipConstInApp_2054_);
v_skipInstances_boxed_2065_ = lean_unbox(v_skipInstances_2055_);
v_res_2066_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_2051_, v_post_2052_, v_usedLetOnly_boxed_2063_, v_skipConstInApp_boxed_2064_, v_skipInstances_boxed_2065_, v_e_2056_, v_a_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v_a_2057_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13___boxed(lean_object* v_pre_2067_, lean_object* v_post_2068_, lean_object* v_usedLetOnly_2069_, lean_object* v_skipConstInApp_2070_, lean_object* v_skipInstances_2071_, lean_object* v_fvars_2072_, lean_object* v_e_2073_, lean_object* v_a_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
uint8_t v_usedLetOnly_boxed_2080_; uint8_t v_skipConstInApp_boxed_2081_; uint8_t v_skipInstances_boxed_2082_; lean_object* v_res_2083_; 
v_usedLetOnly_boxed_2080_ = lean_unbox(v_usedLetOnly_2069_);
v_skipConstInApp_boxed_2081_ = lean_unbox(v_skipConstInApp_2070_);
v_skipInstances_boxed_2082_ = lean_unbox(v_skipInstances_2071_);
v_res_2083_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13(v_pre_2067_, v_post_2068_, v_usedLetOnly_boxed_2080_, v_skipConstInApp_boxed_2081_, v_skipInstances_boxed_2082_, v_fvars_2072_, v_e_2073_, v_a_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v_a_2074_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14___boxed(lean_object* v_pre_2084_, lean_object* v_post_2085_, lean_object* v_usedLetOnly_2086_, lean_object* v_skipConstInApp_2087_, lean_object* v_skipInstances_2088_, lean_object* v_fvars_2089_, lean_object* v_e_2090_, lean_object* v_a_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
uint8_t v_usedLetOnly_boxed_2097_; uint8_t v_skipConstInApp_boxed_2098_; uint8_t v_skipInstances_boxed_2099_; lean_object* v_res_2100_; 
v_usedLetOnly_boxed_2097_ = lean_unbox(v_usedLetOnly_2086_);
v_skipConstInApp_boxed_2098_ = lean_unbox(v_skipConstInApp_2087_);
v_skipInstances_boxed_2099_ = lean_unbox(v_skipInstances_2088_);
v_res_2100_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__14(v_pre_2084_, v_post_2085_, v_usedLetOnly_boxed_2097_, v_skipConstInApp_boxed_2098_, v_skipInstances_boxed_2099_, v_fvars_2089_, v_e_2090_, v_a_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v_a_2091_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15___boxed(lean_object* v_pre_2101_, lean_object* v_post_2102_, lean_object* v_usedLetOnly_2103_, lean_object* v_skipConstInApp_2104_, lean_object* v_skipInstances_2105_, lean_object* v_fvars_2106_, lean_object* v_e_2107_, lean_object* v_a_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
uint8_t v_usedLetOnly_boxed_2114_; uint8_t v_skipConstInApp_boxed_2115_; uint8_t v_skipInstances_boxed_2116_; lean_object* v_res_2117_; 
v_usedLetOnly_boxed_2114_ = lean_unbox(v_usedLetOnly_2103_);
v_skipConstInApp_boxed_2115_ = lean_unbox(v_skipConstInApp_2104_);
v_skipInstances_boxed_2116_ = lean_unbox(v_skipInstances_2105_);
v_res_2117_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15(v_pre_2101_, v_post_2102_, v_usedLetOnly_boxed_2114_, v_skipConstInApp_boxed_2115_, v_skipInstances_boxed_2116_, v_fvars_2106_, v_e_2107_, v_a_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v_a_2108_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_upperBound_2118_, lean_object* v___x_2119_, lean_object* v_pre_2120_, lean_object* v_post_2121_, lean_object* v_usedLetOnly_2122_, lean_object* v_skipConstInApp_2123_, lean_object* v_skipInstances_2124_, lean_object* v_a_2125_, lean_object* v_b_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
uint8_t v_usedLetOnly_boxed_2133_; uint8_t v_skipConstInApp_boxed_2134_; uint8_t v_skipInstances_boxed_2135_; lean_object* v_res_2136_; 
v_usedLetOnly_boxed_2133_ = lean_unbox(v_usedLetOnly_2122_);
v_skipConstInApp_boxed_2134_ = lean_unbox(v_skipConstInApp_2123_);
v_skipInstances_boxed_2135_ = lean_unbox(v_skipInstances_2124_);
v_res_2136_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg(v_upperBound_2118_, v___x_2119_, v_pre_2120_, v_post_2121_, v_usedLetOnly_boxed_2133_, v_skipConstInApp_boxed_2134_, v_skipInstances_boxed_2135_, v_a_2125_, v_b_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___x_2119_);
lean_dec(v_upperBound_2118_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__16___boxed(lean_object* v_skipInstances_2137_, lean_object* v_pre_2138_, lean_object* v_post_2139_, lean_object* v_usedLetOnly_2140_, lean_object* v_skipConstInApp_2141_, lean_object* v_x_2142_, lean_object* v_x_2143_, lean_object* v_x_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
uint8_t v_skipInstances_boxed_2151_; uint8_t v_usedLetOnly_boxed_2152_; uint8_t v_skipConstInApp_boxed_2153_; lean_object* v_res_2154_; 
v_skipInstances_boxed_2151_ = lean_unbox(v_skipInstances_2137_);
v_usedLetOnly_boxed_2152_ = lean_unbox(v_usedLetOnly_2140_);
v_skipConstInApp_boxed_2153_ = lean_unbox(v_skipConstInApp_2141_);
v_res_2154_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__16(v_skipInstances_boxed_2151_, v_pre_2138_, v_post_2139_, v_usedLetOnly_boxed_2152_, v_skipConstInApp_boxed_2153_, v_x_2142_, v_x_2143_, v_x_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
return v_res_2154_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2156_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2156_, 0, lean_box(0));
lean_closure_set(v___x_2156_, 1, lean_box(0));
lean_closure_set(v___x_2156_, 2, v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7(lean_object* v_input_2157_, lean_object* v_pre_2158_, lean_object* v_post_2159_, uint8_t v_usedLetOnly_2160_, uint8_t v_skipConstInApp_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v_a_2169_; uint8_t v___x_2170_; lean_object* v___x_2171_; 
v___x_2167_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0);
v___x_2168_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___lam__0(lean_box(0), v___x_2167_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref(v___x_2168_);
v___x_2170_ = 0;
v___x_2171_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8(v_pre_2158_, v_post_2159_, v_usedLetOnly_2160_, v_skipConstInApp_2161_, v___x_2170_, v_input_2157_, v_a_2169_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref(v___x_2171_);
v___x_2173_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2173_, 0, lean_box(0));
lean_closure_set(v___x_2173_, 1, lean_box(0));
lean_closure_set(v___x_2173_, 2, v_a_2169_);
v___x_2174_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___lam__0(lean_box(0), v___x_2173_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v___x_2174_, 0);
lean_dec(v_unused_2182_);
v___x_2176_ = v___x_2174_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_dec(v___x_2174_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v_a_2172_);
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2172_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
else
{
lean_dec(v_a_2169_);
return v___x_2171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7___boxed(lean_object* v_input_2183_, lean_object* v_pre_2184_, lean_object* v_post_2185_, lean_object* v_usedLetOnly_2186_, lean_object* v_skipConstInApp_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
uint8_t v_usedLetOnly_boxed_2193_; uint8_t v_skipConstInApp_boxed_2194_; lean_object* v_res_2195_; 
v_usedLetOnly_boxed_2193_ = lean_unbox(v_usedLetOnly_2186_);
v_skipConstInApp_boxed_2194_ = lean_unbox(v_skipConstInApp_2187_);
v_res_2195_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7(v_input_2183_, v_pre_2184_, v_post_2185_, v_usedLetOnly_boxed_2193_, v_skipConstInApp_boxed_2194_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
return v_res_2195_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___lam__0(lean_object* v___x_2196_, lean_object* v_x_2197_){
_start:
{
lean_object* v_declName_2198_; uint8_t v___x_2199_; 
v_declName_2198_ = lean_ctor_get(v_x_2197_, 3);
v___x_2199_ = lean_name_eq(v_declName_2198_, v___x_2196_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___lam__0___boxed(lean_object* v___x_2200_, lean_object* v_x_2201_){
_start:
{
uint8_t v_res_2202_; lean_object* v_r_2203_; 
v_res_2202_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___lam__0(v___x_2200_, v_x_2201_);
lean_dec_ref(v_x_2201_);
lean_dec(v___x_2200_);
v_r_2203_ = lean_box(v_res_2202_);
return v_r_2203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__0(lean_object* v_val_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = lean_st_ref_get(v_val_2204_);
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__0___boxed(lean_object* v_val_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__0(v_val_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v_val_2212_);
return v_res_2218_;
}
}
static uint64_t _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0(void){
_start:
{
uint8_t v___x_2219_; uint64_t v___x_2220_; 
v___x_2219_ = 2;
v___x_2220_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg(lean_object* v_upperBound_2221_, lean_object* v_val_2222_, lean_object* v_next_2223_, lean_object* v_params_2224_, lean_object* v___x_2225_, lean_object* v_val_2226_, lean_object* v_next_2227_, uint8_t v___x_2228_, lean_object* v_a_2229_, uint8_t v_b_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
uint8_t v_a_2237_; uint8_t v___x_2241_; 
v___x_2241_ = lean_nat_dec_lt(v_a_2229_, v_upperBound_2221_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_dec(v_a_2229_);
lean_dec(v_next_2227_);
lean_dec_ref(v___x_2225_);
v___x_2242_ = lean_box(v_b_2230_);
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
return v___x_2243_;
}
else
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2244_ = lean_st_ref_get(v_val_2222_);
v___x_2245_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2223_, v_a_2229_, v___x_2244_);
lean_dec(v___x_2244_);
if (v___x_2245_ == 0)
{
v_a_2237_ = v_b_2230_;
goto v___jp_2236_;
}
else
{
lean_object* v___x_2246_; uint8_t v_foApprox_2247_; uint8_t v_ctxApprox_2248_; uint8_t v_quasiPatternApprox_2249_; uint8_t v_constApprox_2250_; uint8_t v_isDefEqStuckEx_2251_; uint8_t v_unificationHints_2252_; uint8_t v_assignSyntheticOpaque_2253_; uint8_t v_offsetCnstrs_2254_; uint8_t v_transparency_2255_; uint8_t v_etaStruct_2256_; uint8_t v_univApprox_2257_; uint8_t v_iota_2258_; uint8_t v_beta_2259_; uint8_t v_proj_2260_; uint8_t v_zeta_2261_; uint8_t v_zetaDelta_2262_; uint8_t v_zetaUnused_2263_; uint8_t v_zetaHave_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2327_; 
v___x_2246_ = l_Lean_Meta_Context_config(v___y_2231_);
v_foApprox_2247_ = lean_ctor_get_uint8(v___x_2246_, 0);
v_ctxApprox_2248_ = lean_ctor_get_uint8(v___x_2246_, 1);
v_quasiPatternApprox_2249_ = lean_ctor_get_uint8(v___x_2246_, 2);
v_constApprox_2250_ = lean_ctor_get_uint8(v___x_2246_, 3);
v_isDefEqStuckEx_2251_ = lean_ctor_get_uint8(v___x_2246_, 4);
v_unificationHints_2252_ = lean_ctor_get_uint8(v___x_2246_, 5);
v_assignSyntheticOpaque_2253_ = lean_ctor_get_uint8(v___x_2246_, 7);
v_offsetCnstrs_2254_ = lean_ctor_get_uint8(v___x_2246_, 8);
v_transparency_2255_ = lean_ctor_get_uint8(v___x_2246_, 9);
v_etaStruct_2256_ = lean_ctor_get_uint8(v___x_2246_, 10);
v_univApprox_2257_ = lean_ctor_get_uint8(v___x_2246_, 11);
v_iota_2258_ = lean_ctor_get_uint8(v___x_2246_, 12);
v_beta_2259_ = lean_ctor_get_uint8(v___x_2246_, 13);
v_proj_2260_ = lean_ctor_get_uint8(v___x_2246_, 14);
v_zeta_2261_ = lean_ctor_get_uint8(v___x_2246_, 15);
v_zetaDelta_2262_ = lean_ctor_get_uint8(v___x_2246_, 16);
v_zetaUnused_2263_ = lean_ctor_get_uint8(v___x_2246_, 17);
v_zetaHave_2264_ = lean_ctor_get_uint8(v___x_2246_, 18);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2266_ = v___x_2246_;
v_isShared_2267_ = v_isSharedCheck_2327_;
goto v_resetjp_2265_;
}
else
{
lean_dec(v___x_2246_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2327_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
uint8_t v_trackZetaDelta_2268_; lean_object* v_zetaDeltaSet_2269_; lean_object* v_lctx_2270_; lean_object* v_localInstances_2271_; lean_object* v_defEqCtx_x3f_2272_; lean_object* v_synthPendingDepth_2273_; lean_object* v_canUnfold_x3f_2274_; uint8_t v_univApprox_2275_; uint8_t v_inTypeClassResolution_2276_; uint8_t v_cacheInferType_2277_; uint8_t v___x_2278_; lean_object* v___x_2280_; 
v_trackZetaDelta_2268_ = lean_ctor_get_uint8(v___y_2231_, sizeof(void*)*7);
v_zetaDeltaSet_2269_ = lean_ctor_get(v___y_2231_, 1);
v_lctx_2270_ = lean_ctor_get(v___y_2231_, 2);
v_localInstances_2271_ = lean_ctor_get(v___y_2231_, 3);
v_defEqCtx_x3f_2272_ = lean_ctor_get(v___y_2231_, 4);
v_synthPendingDepth_2273_ = lean_ctor_get(v___y_2231_, 5);
v_canUnfold_x3f_2274_ = lean_ctor_get(v___y_2231_, 6);
v_univApprox_2275_ = lean_ctor_get_uint8(v___y_2231_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2276_ = lean_ctor_get_uint8(v___y_2231_, sizeof(void*)*7 + 2);
v_cacheInferType_2277_ = lean_ctor_get_uint8(v___y_2231_, sizeof(void*)*7 + 3);
v___x_2278_ = 0;
if (v_isShared_2267_ == 0)
{
v___x_2280_ = v___x_2266_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 0, v_foApprox_2247_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 1, v_ctxApprox_2248_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 2, v_quasiPatternApprox_2249_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 3, v_constApprox_2250_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 4, v_isDefEqStuckEx_2251_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 5, v_unificationHints_2252_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 7, v_assignSyntheticOpaque_2253_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 8, v_offsetCnstrs_2254_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 9, v_transparency_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 10, v_etaStruct_2256_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 11, v_univApprox_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 12, v_iota_2258_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 13, v_beta_2259_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 14, v_proj_2260_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 15, v_zeta_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 16, v_zetaDelta_2262_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 17, v_zetaUnused_2263_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, 18, v_zetaHave_2264_);
v___x_2280_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
uint64_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; uint8_t v_foApprox_2285_; uint8_t v_ctxApprox_2286_; uint8_t v_quasiPatternApprox_2287_; uint8_t v_constApprox_2288_; uint8_t v_isDefEqStuckEx_2289_; uint8_t v_unificationHints_2290_; uint8_t v_proofIrrelevance_2291_; uint8_t v_assignSyntheticOpaque_2292_; uint8_t v_offsetCnstrs_2293_; uint8_t v_etaStruct_2294_; uint8_t v_univApprox_2295_; uint8_t v_iota_2296_; uint8_t v_beta_2297_; uint8_t v_proj_2298_; uint8_t v_zeta_2299_; uint8_t v_zetaDelta_2300_; uint8_t v_zetaUnused_2301_; uint8_t v_zetaHave_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2325_; 
lean_ctor_set_uint8(v___x_2280_, 6, v___x_2278_);
v___x_2281_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2280_);
v___x_2282_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set_uint64(v___x_2282_, sizeof(void*)*1, v___x_2281_);
lean_inc(v_canUnfold_x3f_2274_);
lean_inc(v_synthPendingDepth_2273_);
lean_inc(v_defEqCtx_x3f_2272_);
lean_inc_ref(v_localInstances_2271_);
lean_inc_ref(v_lctx_2270_);
lean_inc(v_zetaDeltaSet_2269_);
v___x_2283_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
lean_ctor_set(v___x_2283_, 1, v_zetaDeltaSet_2269_);
lean_ctor_set(v___x_2283_, 2, v_lctx_2270_);
lean_ctor_set(v___x_2283_, 3, v_localInstances_2271_);
lean_ctor_set(v___x_2283_, 4, v_defEqCtx_x3f_2272_);
lean_ctor_set(v___x_2283_, 5, v_synthPendingDepth_2273_);
lean_ctor_set(v___x_2283_, 6, v_canUnfold_x3f_2274_);
lean_ctor_set_uint8(v___x_2283_, sizeof(void*)*7, v_trackZetaDelta_2268_);
lean_ctor_set_uint8(v___x_2283_, sizeof(void*)*7 + 1, v_univApprox_2275_);
lean_ctor_set_uint8(v___x_2283_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2276_);
lean_ctor_set_uint8(v___x_2283_, sizeof(void*)*7 + 3, v_cacheInferType_2277_);
v___x_2284_ = l_Lean_Meta_Context_config(v___x_2283_);
v_foApprox_2285_ = lean_ctor_get_uint8(v___x_2284_, 0);
v_ctxApprox_2286_ = lean_ctor_get_uint8(v___x_2284_, 1);
v_quasiPatternApprox_2287_ = lean_ctor_get_uint8(v___x_2284_, 2);
v_constApprox_2288_ = lean_ctor_get_uint8(v___x_2284_, 3);
v_isDefEqStuckEx_2289_ = lean_ctor_get_uint8(v___x_2284_, 4);
v_unificationHints_2290_ = lean_ctor_get_uint8(v___x_2284_, 5);
v_proofIrrelevance_2291_ = lean_ctor_get_uint8(v___x_2284_, 6);
v_assignSyntheticOpaque_2292_ = lean_ctor_get_uint8(v___x_2284_, 7);
v_offsetCnstrs_2293_ = lean_ctor_get_uint8(v___x_2284_, 8);
v_etaStruct_2294_ = lean_ctor_get_uint8(v___x_2284_, 10);
v_univApprox_2295_ = lean_ctor_get_uint8(v___x_2284_, 11);
v_iota_2296_ = lean_ctor_get_uint8(v___x_2284_, 12);
v_beta_2297_ = lean_ctor_get_uint8(v___x_2284_, 13);
v_proj_2298_ = lean_ctor_get_uint8(v___x_2284_, 14);
v_zeta_2299_ = lean_ctor_get_uint8(v___x_2284_, 15);
v_zetaDelta_2300_ = lean_ctor_get_uint8(v___x_2284_, 16);
v_zetaUnused_2301_ = lean_ctor_get_uint8(v___x_2284_, 17);
v_zetaHave_2302_ = lean_ctor_get_uint8(v___x_2284_, 18);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2304_ = v___x_2284_;
v_isShared_2305_ = v_isSharedCheck_2325_;
goto v_resetjp_2303_;
}
else
{
lean_dec(v___x_2284_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2325_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; uint8_t v___x_2307_; lean_object* v_config_2309_; 
v___x_2306_ = lean_array_fget_borrowed(v_params_2224_, v_a_2229_);
v___x_2307_ = 2;
if (v_isShared_2305_ == 0)
{
v_config_2309_ = v___x_2304_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 0, v_foApprox_2285_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 1, v_ctxApprox_2286_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 2, v_quasiPatternApprox_2287_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 3, v_constApprox_2288_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 4, v_isDefEqStuckEx_2289_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 5, v_unificationHints_2290_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 6, v_proofIrrelevance_2291_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 7, v_assignSyntheticOpaque_2292_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 8, v_offsetCnstrs_2293_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 10, v_etaStruct_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 11, v_univApprox_2295_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 12, v_iota_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 13, v_beta_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 14, v_proj_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 15, v_zeta_2299_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 16, v_zetaDelta_2300_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 17, v_zetaUnused_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, 18, v_zetaHave_2302_);
v_config_2309_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
uint64_t v___x_2310_; uint64_t v___x_2311_; uint64_t v___x_2312_; uint64_t v___x_2313_; uint64_t v___x_2314_; uint64_t v_key_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_ctor_set_uint8(v_config_2309_, 9, v___x_2307_);
v___x_2310_ = l_Lean_Meta_Context_configKey(v___x_2283_);
lean_dec_ref(v___x_2283_);
v___x_2311_ = 2ULL;
v___x_2312_ = lean_uint64_shift_right(v___x_2310_, v___x_2311_);
v___x_2313_ = lean_uint64_shift_left(v___x_2312_, v___x_2311_);
v___x_2314_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0);
v_key_2315_ = lean_uint64_lor(v___x_2313_, v___x_2314_);
v___x_2316_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2316_, 0, v_config_2309_);
lean_ctor_set_uint64(v___x_2316_, sizeof(void*)*1, v_key_2315_);
lean_inc(v_canUnfold_x3f_2274_);
lean_inc(v_synthPendingDepth_2273_);
lean_inc(v_defEqCtx_x3f_2272_);
lean_inc_ref(v_localInstances_2271_);
lean_inc_ref(v_lctx_2270_);
lean_inc(v_zetaDeltaSet_2269_);
v___x_2317_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v_zetaDeltaSet_2269_);
lean_ctor_set(v___x_2317_, 2, v_lctx_2270_);
lean_ctor_set(v___x_2317_, 3, v_localInstances_2271_);
lean_ctor_set(v___x_2317_, 4, v_defEqCtx_x3f_2272_);
lean_ctor_set(v___x_2317_, 5, v_synthPendingDepth_2273_);
lean_ctor_set(v___x_2317_, 6, v_canUnfold_x3f_2274_);
lean_ctor_set_uint8(v___x_2317_, sizeof(void*)*7, v_trackZetaDelta_2268_);
lean_ctor_set_uint8(v___x_2317_, sizeof(void*)*7 + 1, v_univApprox_2275_);
lean_ctor_set_uint8(v___x_2317_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2276_);
lean_ctor_set_uint8(v___x_2317_, sizeof(void*)*7 + 3, v_cacheInferType_2277_);
lean_inc_ref(v___x_2225_);
lean_inc(v___x_2306_);
v___x_2318_ = l_Lean_Meta_isExprDefEq(v___x_2306_, v___x_2225_, v___x_2317_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec_ref(v___x_2317_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; uint8_t v___x_2320_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___x_2318_);
v___x_2320_ = lean_unbox(v_a_2319_);
lean_dec(v_a_2319_);
if (v___x_2320_ == 0)
{
v_a_2237_ = v_b_2230_;
goto v___jp_2236_;
}
else
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = lean_st_ref_take(v_val_2222_);
lean_inc(v_a_2229_);
lean_inc(v_next_2227_);
v___x_2322_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2226_, v_next_2227_, v_next_2223_, v_a_2229_, v___x_2321_);
v___x_2323_ = lean_st_ref_set(v_val_2222_, v___x_2322_);
v_a_2237_ = v___x_2228_;
goto v___jp_2236_;
}
}
else
{
lean_dec(v_a_2229_);
lean_dec(v_next_2227_);
lean_dec_ref(v___x_2225_);
return v___x_2318_;
}
}
}
}
}
}
}
v___jp_2236_:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_nat_add(v_a_2229_, v___x_2238_);
lean_dec(v_a_2229_);
v_a_2229_ = v___x_2239_;
v_b_2230_ = v_a_2237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___boxed(lean_object* v_upperBound_2328_, lean_object* v_val_2329_, lean_object* v_next_2330_, lean_object* v_params_2331_, lean_object* v___x_2332_, lean_object* v_val_2333_, lean_object* v_next_2334_, lean_object* v___x_2335_, lean_object* v_a_2336_, lean_object* v_b_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
uint8_t v___x_43950__boxed_2343_; uint8_t v_b_boxed_2344_; lean_object* v_res_2345_; 
v___x_43950__boxed_2343_ = lean_unbox(v___x_2335_);
v_b_boxed_2344_ = lean_unbox(v_b_2337_);
v_res_2345_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg(v_upperBound_2328_, v_val_2329_, v_next_2330_, v_params_2331_, v___x_2332_, v_val_2333_, v_next_2334_, v___x_43950__boxed_2343_, v_a_2336_, v_b_boxed_2344_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v_val_2333_);
lean_dec_ref(v_params_2331_);
lean_dec(v_next_2330_);
lean_dec(v_val_2329_);
lean_dec(v_upperBound_2328_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(lean_object* v_msgData_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v_env_2353_; lean_object* v___x_2354_; lean_object* v_mctx_2355_; lean_object* v_lctx_2356_; lean_object* v_options_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2352_ = lean_st_ref_get(v___y_2350_);
v_env_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc_ref(v_env_2353_);
lean_dec(v___x_2352_);
v___x_2354_ = lean_st_ref_get(v___y_2348_);
v_mctx_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc_ref(v_mctx_2355_);
lean_dec(v___x_2354_);
v_lctx_2356_ = lean_ctor_get(v___y_2347_, 2);
v_options_2357_ = lean_ctor_get(v___y_2349_, 2);
lean_inc_ref(v_options_2357_);
lean_inc_ref(v_lctx_2356_);
v___x_2358_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2358_, 0, v_env_2353_);
lean_ctor_set(v___x_2358_, 1, v_mctx_2355_);
lean_ctor_set(v___x_2358_, 2, v_lctx_2356_);
lean_ctor_set(v___x_2358_, 3, v_options_2357_);
v___x_2359_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v_msgData_2346_);
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2___boxed(lean_object* v_msgData_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msgData_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
return v_res_2367_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2368_; double v___x_2369_; 
v___x_2368_ = lean_unsigned_to_nat(0u);
v___x_2369_ = lean_float_of_nat(v___x_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(lean_object* v_cls_2373_, lean_object* v_msg_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_ref_2380_; lean_object* v___x_2381_; lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2426_; 
v_ref_2380_ = lean_ctor_get(v___y_2377_, 5);
v___x_2381_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msg_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2426_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2426_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v_traceState_2387_; lean_object* v_env_2388_; lean_object* v_nextMacroScope_2389_; lean_object* v_ngen_2390_; lean_object* v_auxDeclNGen_2391_; lean_object* v_cache_2392_; lean_object* v_messages_2393_; lean_object* v_infoState_2394_; lean_object* v_snapshotTasks_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2425_; 
v___x_2386_ = lean_st_ref_take(v___y_2378_);
v_traceState_2387_ = lean_ctor_get(v___x_2386_, 4);
v_env_2388_ = lean_ctor_get(v___x_2386_, 0);
v_nextMacroScope_2389_ = lean_ctor_get(v___x_2386_, 1);
v_ngen_2390_ = lean_ctor_get(v___x_2386_, 2);
v_auxDeclNGen_2391_ = lean_ctor_get(v___x_2386_, 3);
v_cache_2392_ = lean_ctor_get(v___x_2386_, 5);
v_messages_2393_ = lean_ctor_get(v___x_2386_, 6);
v_infoState_2394_ = lean_ctor_get(v___x_2386_, 7);
v_snapshotTasks_2395_ = lean_ctor_get(v___x_2386_, 8);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2397_ = v___x_2386_;
v_isShared_2398_ = v_isSharedCheck_2425_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_snapshotTasks_2395_);
lean_inc(v_infoState_2394_);
lean_inc(v_messages_2393_);
lean_inc(v_cache_2392_);
lean_inc(v_traceState_2387_);
lean_inc(v_auxDeclNGen_2391_);
lean_inc(v_ngen_2390_);
lean_inc(v_nextMacroScope_2389_);
lean_inc(v_env_2388_);
lean_dec(v___x_2386_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2425_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
uint64_t v_tid_2399_; lean_object* v_traces_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2424_; 
v_tid_2399_ = lean_ctor_get_uint64(v_traceState_2387_, sizeof(void*)*1);
v_traces_2400_ = lean_ctor_get(v_traceState_2387_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_traceState_2387_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2402_ = v_traceState_2387_;
v_isShared_2403_ = v_isSharedCheck_2424_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_traces_2400_);
lean_dec(v_traceState_2387_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2424_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; double v___x_2405_; uint8_t v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2404_ = lean_box(0);
v___x_2405_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0);
v___x_2406_ = 0;
v___x_2407_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1));
v___x_2408_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2408_, 0, v_cls_2373_);
lean_ctor_set(v___x_2408_, 1, v___x_2404_);
lean_ctor_set(v___x_2408_, 2, v___x_2407_);
lean_ctor_set_float(v___x_2408_, sizeof(void*)*3, v___x_2405_);
lean_ctor_set_float(v___x_2408_, sizeof(void*)*3 + 8, v___x_2405_);
lean_ctor_set_uint8(v___x_2408_, sizeof(void*)*3 + 16, v___x_2406_);
v___x_2409_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2));
v___x_2410_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v_a_2382_);
lean_ctor_set(v___x_2410_, 2, v___x_2409_);
lean_inc(v_ref_2380_);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v_ref_2380_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = l_Lean_PersistentArray_push___redArg(v_traces_2400_, v___x_2411_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2412_);
v___x_2414_ = v___x_2402_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2412_);
lean_ctor_set_uint64(v_reuseFailAlloc_2423_, sizeof(void*)*1, v_tid_2399_);
v___x_2414_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 4, v___x_2414_);
v___x_2416_ = v___x_2397_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_env_2388_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_nextMacroScope_2389_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_ngen_2390_);
lean_ctor_set(v_reuseFailAlloc_2422_, 3, v_auxDeclNGen_2391_);
lean_ctor_set(v_reuseFailAlloc_2422_, 4, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2422_, 5, v_cache_2392_);
lean_ctor_set(v_reuseFailAlloc_2422_, 6, v_messages_2393_);
lean_ctor_set(v_reuseFailAlloc_2422_, 7, v_infoState_2394_);
lean_ctor_set(v_reuseFailAlloc_2422_, 8, v_snapshotTasks_2395_);
v___x_2416_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2420_; 
v___x_2417_ = lean_st_ref_set(v___y_2378_, v___x_2416_);
v___x_2418_ = lean_box(0);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2418_);
v___x_2420_ = v___x_2384_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___boxed(lean_object* v_cls_2427_, lean_object* v_msg_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v_cls_2427_, v_msg_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(lean_object* v_val_2435_, lean_object* v_val_2436_, lean_object* v_a_2437_, lean_object* v___x_2438_, lean_object* v_____r_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2445_ = lean_st_ref_take(v_val_2435_);
v___x_2446_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2436_, v_a_2437_, v___x_2445_);
v___x_2447_ = lean_st_ref_set(v_val_2435_, v___x_2446_);
v___x_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2438_);
v___x_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1___boxed(lean_object* v_val_2450_, lean_object* v_val_2451_, lean_object* v_a_2452_, lean_object* v___x_2453_, lean_object* v_____r_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2450_, v_val_2451_, v_a_2452_, v___x_2453_, v_____r_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v_val_2451_);
lean_dec(v_val_2450_);
return v_res_2460_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3));
v___x_2472_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__5));
v___x_2473_ = l_Lean_Name_append(v___x_2472_, v___x_2471_);
return v___x_2473_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__7));
v___x_2476_ = l_Lean_stringToMessageData(v___x_2475_);
return v___x_2476_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2478_ = l_Lean_stringToMessageData(v___x_2477_);
return v___x_2478_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__10));
v___x_2481_ = l_Lean_stringToMessageData(v___x_2480_);
return v___x_2481_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__12));
v___x_2484_ = l_Lean_stringToMessageData(v___x_2483_);
return v___x_2484_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__14));
v___x_2487_ = l_Lean_stringToMessageData(v___x_2486_);
return v___x_2487_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__16));
v___x_2490_ = l_Lean_stringToMessageData(v___x_2489_);
return v___x_2490_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__18));
v___x_2493_ = l_Lean_stringToMessageData(v___x_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_val_2494_, lean_object* v_val_2495_, lean_object* v_upperBound_2496_, lean_object* v_args_2497_, lean_object* v_e_2498_, lean_object* v_next_2499_, lean_object* v_params_2500_, lean_object* v___x_2501_, uint8_t v___x_2502_, lean_object* v_a_2503_, lean_object* v_b_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_a_2511_; lean_object* v___y_2516_; uint8_t v___x_2535_; 
v___x_2535_ = lean_nat_dec_lt(v_a_2503_, v_upperBound_2496_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; 
lean_dec(v_a_2503_);
lean_dec_ref(v_e_2498_);
lean_dec(v_val_2495_);
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_b_2504_);
return v___x_2536_;
}
else
{
lean_object* v___x_2537_; 
v___x_2537_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__0(v_val_2494_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref(v___x_2537_);
v___x_2539_ = lean_box(0);
v___x_2540_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2495_, v_a_2503_, v_a_2538_);
lean_dec(v_a_2538_);
if (v___x_2540_ == 0)
{
v_a_2511_ = v___x_2539_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2541_ = lean_array_get_size(v_args_2497_);
v___x_2542_ = lean_nat_dec_lt(v_a_2503_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_object* v_options_2543_; lean_object* v_inheritedTraceOptions_2544_; uint8_t v_hasTrace_2545_; 
v_options_2543_ = lean_ctor_get(v___y_2507_, 2);
v_inheritedTraceOptions_2544_ = lean_ctor_get(v___y_2507_, 13);
v_hasTrace_2545_ = lean_ctor_get_uint8(v_options_2543_, sizeof(void*)*1);
if (v_hasTrace_2545_ == 0)
{
goto v___jp_2546_;
}
else
{
lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2548_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3));
v___x_2549_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6);
v___x_2550_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2544_, v_options_2543_, v___x_2549_);
if (v___x_2550_ == 0)
{
goto v___jp_2546_;
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2551_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8);
lean_inc(v_val_2495_);
v___x_2552_ = l_Nat_reprFast(v_val_2495_);
v___x_2553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
v___x_2554_ = l_Lean_MessageData_ofFormat(v___x_2553_);
v___x_2555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2551_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9);
v___x_2557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
lean_inc(v_a_2503_);
v___x_2558_ = l_Nat_reprFast(v_a_2503_);
v___x_2559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
v___x_2560_ = l_Lean_MessageData_ofFormat(v___x_2559_);
lean_inc_ref(v___x_2560_);
v___x_2561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2557_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11);
v___x_2563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
lean_inc_ref(v_e_2498_);
v___x_2564_ = l_Lean_MessageData_ofExpr(v_e_2498_);
v___x_2565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2563_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__13);
v___x_2567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v___x_2560_);
v___x_2569_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2548_, v___x_2568_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2571_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref(v___x_2569_);
lean_inc(v_a_2503_);
v___x_2571_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2494_, v_val_2495_, v_a_2503_, v___x_2539_, v_a_2570_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
v___y_2516_ = v___x_2571_;
goto v___jp_2515_;
}
else
{
lean_dec(v_a_2503_);
lean_dec_ref(v_e_2498_);
lean_dec(v_val_2495_);
return v___x_2569_;
}
}
}
v___jp_2546_:
{
lean_object* v___x_2547_; 
lean_inc(v_a_2503_);
v___x_2547_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2494_, v_val_2495_, v_a_2503_, v___x_2539_, v___x_2539_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
v___y_2516_ = v___x_2547_;
goto v___jp_2515_;
}
}
else
{
lean_object* v___x_2572_; 
v___x_2572_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__0(v_val_2494_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref(v___x_2572_);
v___x_2574_ = lean_array_fget_borrowed(v_args_2497_, v_a_2503_);
v___x_2575_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2495_, v_a_2503_, v_next_2499_, v_a_2573_);
lean_dec(v_a_2573_);
if (lean_obj_tag(v___x_2575_) == 1)
{
lean_object* v_val_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2704_; 
v_val_2576_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2578_ = v___x_2575_;
v_isShared_2579_ = v_isSharedCheck_2704_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_val_2576_);
lean_dec(v___x_2575_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2704_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; uint8_t v_foApprox_2581_; uint8_t v_ctxApprox_2582_; uint8_t v_quasiPatternApprox_2583_; uint8_t v_constApprox_2584_; uint8_t v_isDefEqStuckEx_2585_; uint8_t v_unificationHints_2586_; uint8_t v_assignSyntheticOpaque_2587_; uint8_t v_offsetCnstrs_2588_; uint8_t v_transparency_2589_; uint8_t v_etaStruct_2590_; uint8_t v_univApprox_2591_; uint8_t v_iota_2592_; uint8_t v_beta_2593_; uint8_t v_proj_2594_; uint8_t v_zeta_2595_; uint8_t v_zetaDelta_2596_; uint8_t v_zetaUnused_2597_; uint8_t v_zetaHave_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2703_; 
v___x_2580_ = l_Lean_Meta_Context_config(v___y_2505_);
v_foApprox_2581_ = lean_ctor_get_uint8(v___x_2580_, 0);
v_ctxApprox_2582_ = lean_ctor_get_uint8(v___x_2580_, 1);
v_quasiPatternApprox_2583_ = lean_ctor_get_uint8(v___x_2580_, 2);
v_constApprox_2584_ = lean_ctor_get_uint8(v___x_2580_, 3);
v_isDefEqStuckEx_2585_ = lean_ctor_get_uint8(v___x_2580_, 4);
v_unificationHints_2586_ = lean_ctor_get_uint8(v___x_2580_, 5);
v_assignSyntheticOpaque_2587_ = lean_ctor_get_uint8(v___x_2580_, 7);
v_offsetCnstrs_2588_ = lean_ctor_get_uint8(v___x_2580_, 8);
v_transparency_2589_ = lean_ctor_get_uint8(v___x_2580_, 9);
v_etaStruct_2590_ = lean_ctor_get_uint8(v___x_2580_, 10);
v_univApprox_2591_ = lean_ctor_get_uint8(v___x_2580_, 11);
v_iota_2592_ = lean_ctor_get_uint8(v___x_2580_, 12);
v_beta_2593_ = lean_ctor_get_uint8(v___x_2580_, 13);
v_proj_2594_ = lean_ctor_get_uint8(v___x_2580_, 14);
v_zeta_2595_ = lean_ctor_get_uint8(v___x_2580_, 15);
v_zetaDelta_2596_ = lean_ctor_get_uint8(v___x_2580_, 16);
v_zetaUnused_2597_ = lean_ctor_get_uint8(v___x_2580_, 17);
v_zetaHave_2598_ = lean_ctor_get_uint8(v___x_2580_, 18);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2600_ = v___x_2580_;
v_isShared_2601_ = v_isSharedCheck_2703_;
goto v_resetjp_2599_;
}
else
{
lean_dec(v___x_2580_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2703_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
uint8_t v_trackZetaDelta_2602_; lean_object* v_zetaDeltaSet_2603_; lean_object* v_lctx_2604_; lean_object* v_localInstances_2605_; lean_object* v_defEqCtx_x3f_2606_; lean_object* v_synthPendingDepth_2607_; lean_object* v_canUnfold_x3f_2608_; uint8_t v_univApprox_2609_; uint8_t v_inTypeClassResolution_2610_; uint8_t v_cacheInferType_2611_; uint8_t v___x_2612_; lean_object* v___x_2614_; 
v_trackZetaDelta_2602_ = lean_ctor_get_uint8(v___y_2505_, sizeof(void*)*7);
v_zetaDeltaSet_2603_ = lean_ctor_get(v___y_2505_, 1);
v_lctx_2604_ = lean_ctor_get(v___y_2505_, 2);
v_localInstances_2605_ = lean_ctor_get(v___y_2505_, 3);
v_defEqCtx_x3f_2606_ = lean_ctor_get(v___y_2505_, 4);
v_synthPendingDepth_2607_ = lean_ctor_get(v___y_2505_, 5);
v_canUnfold_x3f_2608_ = lean_ctor_get(v___y_2505_, 6);
v_univApprox_2609_ = lean_ctor_get_uint8(v___y_2505_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2610_ = lean_ctor_get_uint8(v___y_2505_, sizeof(void*)*7 + 2);
v_cacheInferType_2611_ = lean_ctor_get_uint8(v___y_2505_, sizeof(void*)*7 + 3);
v___x_2612_ = 0;
if (v_isShared_2601_ == 0)
{
v___x_2614_ = v___x_2600_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 0, v_foApprox_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 1, v_ctxApprox_2582_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 2, v_quasiPatternApprox_2583_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 3, v_constApprox_2584_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 4, v_isDefEqStuckEx_2585_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 5, v_unificationHints_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 7, v_assignSyntheticOpaque_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 8, v_offsetCnstrs_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 9, v_transparency_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 10, v_etaStruct_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 11, v_univApprox_2591_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 12, v_iota_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 13, v_beta_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 14, v_proj_2594_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 15, v_zeta_2595_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 16, v_zetaDelta_2596_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 17, v_zetaUnused_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, 18, v_zetaHave_2598_);
v___x_2614_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
uint64_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; uint8_t v_foApprox_2619_; uint8_t v_ctxApprox_2620_; uint8_t v_quasiPatternApprox_2621_; uint8_t v_constApprox_2622_; uint8_t v_isDefEqStuckEx_2623_; uint8_t v_unificationHints_2624_; uint8_t v_proofIrrelevance_2625_; uint8_t v_assignSyntheticOpaque_2626_; uint8_t v_offsetCnstrs_2627_; uint8_t v_etaStruct_2628_; uint8_t v_univApprox_2629_; uint8_t v_iota_2630_; uint8_t v_beta_2631_; uint8_t v_proj_2632_; uint8_t v_zeta_2633_; uint8_t v_zetaDelta_2634_; uint8_t v_zetaUnused_2635_; uint8_t v_zetaHave_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2701_; 
lean_ctor_set_uint8(v___x_2614_, 6, v___x_2612_);
v___x_2615_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2614_);
v___x_2616_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2616_, 0, v___x_2614_);
lean_ctor_set_uint64(v___x_2616_, sizeof(void*)*1, v___x_2615_);
lean_inc(v_canUnfold_x3f_2608_);
lean_inc(v_synthPendingDepth_2607_);
lean_inc(v_defEqCtx_x3f_2606_);
lean_inc_ref(v_localInstances_2605_);
lean_inc_ref(v_lctx_2604_);
lean_inc(v_zetaDeltaSet_2603_);
v___x_2617_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
lean_ctor_set(v___x_2617_, 1, v_zetaDeltaSet_2603_);
lean_ctor_set(v___x_2617_, 2, v_lctx_2604_);
lean_ctor_set(v___x_2617_, 3, v_localInstances_2605_);
lean_ctor_set(v___x_2617_, 4, v_defEqCtx_x3f_2606_);
lean_ctor_set(v___x_2617_, 5, v_synthPendingDepth_2607_);
lean_ctor_set(v___x_2617_, 6, v_canUnfold_x3f_2608_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*7, v_trackZetaDelta_2602_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*7 + 1, v_univApprox_2609_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2610_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*7 + 3, v_cacheInferType_2611_);
v___x_2618_ = l_Lean_Meta_Context_config(v___x_2617_);
v_foApprox_2619_ = lean_ctor_get_uint8(v___x_2618_, 0);
v_ctxApprox_2620_ = lean_ctor_get_uint8(v___x_2618_, 1);
v_quasiPatternApprox_2621_ = lean_ctor_get_uint8(v___x_2618_, 2);
v_constApprox_2622_ = lean_ctor_get_uint8(v___x_2618_, 3);
v_isDefEqStuckEx_2623_ = lean_ctor_get_uint8(v___x_2618_, 4);
v_unificationHints_2624_ = lean_ctor_get_uint8(v___x_2618_, 5);
v_proofIrrelevance_2625_ = lean_ctor_get_uint8(v___x_2618_, 6);
v_assignSyntheticOpaque_2626_ = lean_ctor_get_uint8(v___x_2618_, 7);
v_offsetCnstrs_2627_ = lean_ctor_get_uint8(v___x_2618_, 8);
v_etaStruct_2628_ = lean_ctor_get_uint8(v___x_2618_, 10);
v_univApprox_2629_ = lean_ctor_get_uint8(v___x_2618_, 11);
v_iota_2630_ = lean_ctor_get_uint8(v___x_2618_, 12);
v_beta_2631_ = lean_ctor_get_uint8(v___x_2618_, 13);
v_proj_2632_ = lean_ctor_get_uint8(v___x_2618_, 14);
v_zeta_2633_ = lean_ctor_get_uint8(v___x_2618_, 15);
v_zetaDelta_2634_ = lean_ctor_get_uint8(v___x_2618_, 16);
v_zetaUnused_2635_ = lean_ctor_get_uint8(v___x_2618_, 17);
v_zetaHave_2636_ = lean_ctor_get_uint8(v___x_2618_, 18);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2638_ = v___x_2618_;
v_isShared_2639_ = v_isSharedCheck_2701_;
goto v_resetjp_2637_;
}
else
{
lean_dec(v___x_2618_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2701_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; lean_object* v_config_2644_; 
v___x_2640_ = l_Lean_instInhabitedExpr;
v___x_2641_ = lean_array_get_borrowed(v___x_2640_, v_params_2500_, v_val_2576_);
lean_dec(v_val_2576_);
v___x_2642_ = 2;
if (v_isShared_2639_ == 0)
{
v_config_2644_ = v___x_2638_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 0, v_foApprox_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 1, v_ctxApprox_2620_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 2, v_quasiPatternApprox_2621_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 3, v_constApprox_2622_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 4, v_isDefEqStuckEx_2623_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 5, v_unificationHints_2624_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 6, v_proofIrrelevance_2625_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 7, v_assignSyntheticOpaque_2626_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 8, v_offsetCnstrs_2627_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 10, v_etaStruct_2628_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 11, v_univApprox_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 12, v_iota_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 13, v_beta_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 14, v_proj_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 15, v_zeta_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 16, v_zetaDelta_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 17, v_zetaUnused_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, 18, v_zetaHave_2636_);
v_config_2644_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
uint64_t v___x_2645_; uint64_t v___x_2646_; uint64_t v___x_2647_; uint64_t v___x_2648_; uint64_t v___x_2649_; uint64_t v_key_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
lean_ctor_set_uint8(v_config_2644_, 9, v___x_2642_);
v___x_2645_ = l_Lean_Meta_Context_configKey(v___x_2617_);
lean_dec_ref(v___x_2617_);
v___x_2646_ = 2ULL;
v___x_2647_ = lean_uint64_shift_right(v___x_2645_, v___x_2646_);
v___x_2648_ = lean_uint64_shift_left(v___x_2647_, v___x_2646_);
v___x_2649_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg___closed__0);
v_key_2650_ = lean_uint64_lor(v___x_2648_, v___x_2649_);
v___x_2651_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2651_, 0, v_config_2644_);
lean_ctor_set_uint64(v___x_2651_, sizeof(void*)*1, v_key_2650_);
lean_inc(v_canUnfold_x3f_2608_);
lean_inc(v_synthPendingDepth_2607_);
lean_inc(v_defEqCtx_x3f_2606_);
lean_inc_ref(v_localInstances_2605_);
lean_inc_ref(v_lctx_2604_);
lean_inc(v_zetaDeltaSet_2603_);
v___x_2652_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
lean_ctor_set(v___x_2652_, 1, v_zetaDeltaSet_2603_);
lean_ctor_set(v___x_2652_, 2, v_lctx_2604_);
lean_ctor_set(v___x_2652_, 3, v_localInstances_2605_);
lean_ctor_set(v___x_2652_, 4, v_defEqCtx_x3f_2606_);
lean_ctor_set(v___x_2652_, 5, v_synthPendingDepth_2607_);
lean_ctor_set(v___x_2652_, 6, v_canUnfold_x3f_2608_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*7, v_trackZetaDelta_2602_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*7 + 1, v_univApprox_2609_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2610_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*7 + 3, v_cacheInferType_2611_);
lean_inc(v___x_2574_);
lean_inc(v___x_2641_);
v___x_2653_ = l_Lean_Meta_isExprDefEq(v___x_2641_, v___x_2574_, v___x_2652_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec_ref(v___x_2652_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; uint8_t v___x_2655_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref(v___x_2653_);
v___x_2655_ = lean_unbox(v_a_2654_);
lean_dec(v_a_2654_);
if (v___x_2655_ == 0)
{
lean_object* v_options_2656_; lean_object* v_inheritedTraceOptions_2657_; uint8_t v_hasTrace_2658_; 
v_options_2656_ = lean_ctor_get(v___y_2507_, 2);
v_inheritedTraceOptions_2657_ = lean_ctor_get(v___y_2507_, 13);
v_hasTrace_2658_ = lean_ctor_get_uint8(v_options_2656_, sizeof(void*)*1);
if (v_hasTrace_2658_ == 0)
{
lean_del_object(v___x_2578_);
goto v___jp_2659_;
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2661_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3));
v___x_2662_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6);
v___x_2663_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2657_, v_options_2656_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_del_object(v___x_2578_);
goto v___jp_2659_;
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2664_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8);
lean_inc(v_val_2495_);
v___x_2665_ = l_Nat_reprFast(v_val_2495_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set_tag(v___x_2578_, 3);
lean_ctor_set(v___x_2578_, 0, v___x_2665_);
v___x_2667_ = v___x_2578_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2668_ = l_Lean_MessageData_ofFormat(v___x_2667_);
v___x_2669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2664_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9);
v___x_2671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
lean_inc(v_a_2503_);
v___x_2672_ = l_Nat_reprFast(v_a_2503_);
v___x_2673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
v___x_2674_ = l_Lean_MessageData_ofFormat(v___x_2673_);
v___x_2675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2671_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
v___x_2676_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11);
v___x_2677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2675_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
lean_inc_ref(v_e_2498_);
v___x_2678_ = l_Lean_MessageData_ofExpr(v_e_2498_);
v___x_2679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15);
v___x_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2679_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
lean_inc(v___x_2641_);
v___x_2682_ = l_Lean_MessageData_ofExpr(v___x_2641_);
v___x_2683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2681_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__17);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
lean_inc(v___x_2574_);
v___x_2686_ = l_Lean_MessageData_ofExpr(v___x_2574_);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2661_, v___x_2687_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2690_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref(v___x_2688_);
lean_inc(v_a_2503_);
v___x_2690_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2494_, v_val_2495_, v_a_2503_, v___x_2539_, v_a_2689_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
v___y_2516_ = v___x_2690_;
goto v___jp_2515_;
}
else
{
lean_dec(v_a_2503_);
lean_dec_ref(v_e_2498_);
lean_dec(v_val_2495_);
return v___x_2688_;
}
}
}
}
v___jp_2659_:
{
lean_object* v___x_2660_; 
lean_inc(v_a_2503_);
v___x_2660_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2494_, v_val_2495_, v_a_2503_, v___x_2539_, v___x_2539_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
v___y_2516_ = v___x_2660_;
goto v___jp_2515_;
}
}
else
{
lean_del_object(v___x_2578_);
v_a_2511_ = v___x_2539_;
goto v___jp_2510_;
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_del_object(v___x_2578_);
lean_dec(v_a_2503_);
lean_dec_ref(v_e_2498_);
lean_dec(v_val_2495_);
v_a_2692_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2653_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2653_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
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
}
}
}
}
else
{
lean_object* v___x_2705_; uint8_t v___x_2706_; lean_object* v___x_2707_; 
lean_dec(v___x_2575_);
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = 0;
lean_inc(v_a_2503_);
lean_inc(v___x_2574_);
v___x_2707_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg(v___x_2501_, v_val_2494_, v_next_2499_, v_params_2500_, v___x_2574_, v_val_2495_, v_a_2503_, v___x_2502_, v___x_2705_, v___x_2706_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; uint8_t v___x_2709_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref(v___x_2707_);
v___x_2709_ = lean_unbox(v_a_2708_);
lean_dec(v_a_2708_);
if (v___x_2709_ == 0)
{
lean_object* v_options_2710_; lean_object* v_inheritedTraceOptions_2711_; uint8_t v_hasTrace_2712_; 
v_options_2710_ = lean_ctor_get(v___y_2507_, 2);
v_inheritedTraceOptions_2711_ = lean_ctor_get(v___y_2507_, 13);
v_hasTrace_2712_ = lean_ctor_get_uint8(v_options_2710_, sizeof(void*)*1);
if (v_hasTrace_2712_ == 0)
{
goto v___jp_2713_;
}
else
{
lean_object* v___x_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; 
v___x_2715_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3));
v___x_2716_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6);
v___x_2717_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2711_, v_options_2710_, v___x_2716_);
if (v___x_2717_ == 0)
{
goto v___jp_2713_;
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2718_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__8);
lean_inc(v_val_2495_);
v___x_2719_ = l_Nat_reprFast(v_val_2495_);
v___x_2720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
v___x_2721_ = l_Lean_MessageData_ofFormat(v___x_2720_);
v___x_2722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2718_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v___x_2723_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__9);
v___x_2724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2722_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
lean_inc(v_a_2503_);
v___x_2725_ = l_Nat_reprFast(v_a_2503_);
v___x_2726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
v___x_2727_ = l_Lean_MessageData_ofFormat(v___x_2726_);
v___x_2728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2724_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__11);
v___x_2730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2728_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
lean_inc_ref(v_e_2498_);
v___x_2731_ = l_Lean_MessageData_ofExpr(v_e_2498_);
v___x_2732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2730_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__15);
v___x_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
lean_inc(v___x_2574_);
v___x_2735_ = l_Lean_MessageData_ofExpr(v___x_2574_);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2734_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__19);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2715_, v___x_2738_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2741_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref(v___x_2739_);
lean_inc(v_a_2503_);
v___x_2741_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2494_, v_val_2495_, v_a_2503_, v___x_2539_, v_a_2740_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
v___y_2516_ = v___x_2741_;
goto v___jp_2515_;
}
else
{
lean_dec(v_a_2503_);
lean_dec_ref(v_e_2498_);
lean_dec(v_val_2495_);
return v___x_2739_;
}
}
}
v___jp_2713_:
{
lean_object* v___x_2714_; 
lean_inc(v_a_2503_);
v___x_2714_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___lam__1(v_val_2494_, v_val_2495_, v_a_2503_, v___x_2539_, v___x_2539_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
v___y_2516_ = v___x_2714_;
goto v___jp_2515_;
}
}
else
{
v_a_2511_ = v___x_2539_;
goto v___jp_2510_;
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_a_2503_);
lean_dec_ref(v_e_2498_);
lean_dec(v_val_2495_);
v_a_2742_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2707_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2707_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_a_2503_);
lean_dec_ref(v_e_2498_);
lean_dec(v_val_2495_);
v_a_2750_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2572_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2572_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_a_2503_);
lean_dec_ref(v_e_2498_);
lean_dec(v_val_2495_);
v_a_2758_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2537_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2537_);
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
v___jp_2510_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_unsigned_to_nat(1u);
v___x_2513_ = lean_nat_add(v_a_2503_, v___x_2512_);
lean_dec(v_a_2503_);
v_a_2503_ = v___x_2513_;
v_b_2504_ = v_a_2511_;
goto _start;
}
v___jp_2515_:
{
if (lean_obj_tag(v___y_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2526_; 
v_a_2517_ = lean_ctor_get(v___y_2516_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___y_2516_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2519_ = v___y_2516_;
v_isShared_2520_ = v_isSharedCheck_2526_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___y_2516_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2526_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
if (lean_obj_tag(v_a_2517_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2523_; 
lean_dec(v_a_2503_);
lean_dec_ref(v_e_2498_);
lean_dec(v_val_2495_);
v_a_2521_ = lean_ctor_get(v_a_2517_, 0);
lean_inc(v_a_2521_);
lean_dec_ref(v_a_2517_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 0, v_a_2521_);
v___x_2523_ = v___x_2519_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
else
{
lean_object* v_a_2525_; 
lean_del_object(v___x_2519_);
v_a_2525_ = lean_ctor_get(v_a_2517_, 0);
lean_inc(v_a_2525_);
lean_dec_ref(v_a_2517_);
v_a_2511_ = v_a_2525_;
goto v___jp_2510_;
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v_a_2503_);
lean_dec_ref(v_e_2498_);
lean_dec(v_val_2495_);
v_a_2527_ = lean_ctor_get(v___y_2516_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___y_2516_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___y_2516_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___y_2516_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_val_2766_, lean_object* v_val_2767_, lean_object* v_upperBound_2768_, lean_object* v_args_2769_, lean_object* v_e_2770_, lean_object* v_next_2771_, lean_object* v_params_2772_, lean_object* v___x_2773_, lean_object* v___x_2774_, lean_object* v_a_2775_, lean_object* v_b_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
uint8_t v___x_44350__boxed_2782_; lean_object* v_res_2783_; 
v___x_44350__boxed_2782_ = lean_unbox(v___x_2774_);
v_res_2783_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2766_, v_val_2767_, v_upperBound_2768_, v_args_2769_, v_e_2770_, v_next_2771_, v_params_2772_, v___x_2773_, v___x_44350__boxed_2782_, v_a_2775_, v_b_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___x_2773_);
lean_dec_ref(v_params_2772_);
lean_dec(v_next_2771_);
lean_dec_ref(v_args_2769_);
lean_dec(v_upperBound_2768_);
lean_dec(v_val_2766_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_preDefs_2786_, lean_object* v___x_2787_, lean_object* v_val_2788_, lean_object* v_e_2789_, lean_object* v_next_2790_, lean_object* v_params_2791_, lean_object* v___x_2792_, lean_object* v_x_2793_, lean_object* v_x_2794_, lean_object* v_x_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
if (lean_obj_tag(v_x_2793_) == 5)
{
lean_object* v_fn_2801_; lean_object* v_arg_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_fn_2801_ = lean_ctor_get(v_x_2793_, 0);
lean_inc_ref(v_fn_2801_);
v_arg_2802_ = lean_ctor_get(v_x_2793_, 1);
lean_inc_ref(v_arg_2802_);
lean_dec_ref(v_x_2793_);
v___x_2803_ = lean_array_set(v_x_2794_, v_x_2795_, v_arg_2802_);
v___x_2804_ = lean_unsigned_to_nat(1u);
v___x_2805_ = lean_nat_sub(v_x_2795_, v___x_2804_);
lean_dec(v_x_2795_);
v_x_2793_ = v_fn_2801_;
v_x_2794_ = v___x_2803_;
v_x_2795_ = v___x_2805_;
goto _start;
}
else
{
uint8_t v___x_2807_; 
lean_dec(v_x_2795_);
v___x_2807_ = l_Lean_Expr_isConst(v_x_2793_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
lean_dec_ref(v_x_2794_);
lean_dec_ref(v_x_2793_);
lean_dec_ref(v_e_2789_);
v___x_2808_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___closed__0));
v___x_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
return v___x_2809_;
}
else
{
lean_object* v___x_2810_; lean_object* v___f_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2810_ = l_Lean_Expr_constName_x21(v_x_2793_);
lean_dec_ref(v_x_2793_);
v___f_2811_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2811_, 0, v___x_2810_);
v___x_2812_ = lean_unsigned_to_nat(0u);
v___x_2813_ = l_Array_findIdx_x3f_loop___redArg(v___f_2811_, v_preDefs_2786_, v___x_2812_);
if (lean_obj_tag(v___x_2813_) == 1)
{
lean_object* v_val_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_val_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_val_2814_);
lean_dec_ref(v___x_2813_);
v___x_2815_ = lean_box(0);
v___x_2816_ = lean_array_get_borrowed(v___x_2812_, v___x_2787_, v_val_2814_);
v___x_2817_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2788_, v_val_2814_, v___x_2816_, v_x_2794_, v_e_2789_, v_next_2790_, v_params_2791_, v___x_2792_, v___x_2807_, v___x_2812_, v___x_2815_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec_ref(v_x_2794_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2825_; 
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v___x_2817_, 0);
lean_dec(v_unused_2826_);
v___x_2819_ = v___x_2817_;
v_isShared_2820_ = v_isSharedCheck_2825_;
goto v_resetjp_2818_;
}
else
{
lean_dec(v___x_2817_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2825_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2821_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___closed__0));
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2821_);
v___x_2823_ = v___x_2819_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
v_a_2827_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2817_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2817_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
lean_dec(v___x_2813_);
lean_dec_ref(v_x_2794_);
lean_dec_ref(v_e_2789_);
v___x_2835_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___closed__0));
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
return v___x_2836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object* v_preDefs_2837_, lean_object* v___x_2838_, lean_object* v_val_2839_, lean_object* v_e_2840_, lean_object* v_next_2841_, lean_object* v_params_2842_, lean_object* v___x_2843_, lean_object* v_x_2844_, lean_object* v_x_2845_, lean_object* v_x_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_preDefs_2837_, v___x_2838_, v_val_2839_, v_e_2840_, v_next_2841_, v_params_2842_, v___x_2843_, v_x_2844_, v_x_2845_, v_x_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___x_2843_);
lean_dec_ref(v_params_2842_);
lean_dec(v_next_2841_);
lean_dec(v_val_2839_);
lean_dec_ref(v___x_2838_);
lean_dec_ref(v_preDefs_2837_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__1(lean_object* v_preDefs_2853_, lean_object* v___x_2854_, lean_object* v_val_2855_, lean_object* v_a_2856_, lean_object* v_params_2857_, lean_object* v___x_2858_, lean_object* v_e_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_dummy_2865_; lean_object* v_nargs_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v_dummy_2865_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8___lam__1___closed__1);
v_nargs_2866_ = l_Lean_Expr_getAppNumArgs(v_e_2859_);
lean_inc(v_nargs_2866_);
v___x_2867_ = lean_mk_array(v_nargs_2866_, v_dummy_2865_);
v___x_2868_ = lean_unsigned_to_nat(1u);
v___x_2869_ = lean_nat_sub(v_nargs_2866_, v___x_2868_);
lean_dec(v_nargs_2866_);
lean_inc_ref(v_e_2859_);
v___x_2870_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_preDefs_2853_, v___x_2854_, v_val_2855_, v_e_2859_, v_a_2856_, v_params_2857_, v___x_2858_, v_e_2859_, v___x_2867_, v___x_2869_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__1___boxed(lean_object* v_preDefs_2871_, lean_object* v___x_2872_, lean_object* v_val_2873_, lean_object* v_a_2874_, lean_object* v_params_2875_, lean_object* v___x_2876_, lean_object* v_e_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__1(v_preDefs_2871_, v___x_2872_, v_val_2873_, v_a_2874_, v_params_2875_, v___x_2876_, v_e_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___x_2876_);
lean_dec_ref(v_params_2875_);
lean_dec(v_a_2874_);
lean_dec(v_val_2873_);
lean_dec_ref(v___x_2872_);
lean_dec_ref(v_preDefs_2871_);
return v_res_2883_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2887_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__2));
v___x_2888_ = lean_unsigned_to_nat(6u);
v___x_2889_ = lean_unsigned_to_nat(201u);
v___x_2890_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__1));
v___x_2891_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_2892_ = l_mkPanicMessageWithDecl(v___x_2891_, v___x_2890_, v___x_2889_, v___x_2888_, v___x_2887_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2(lean_object* v___x_2893_, lean_object* v___x_2894_, lean_object* v_a_2895_, lean_object* v_preDefs_2896_, lean_object* v_val_2897_, lean_object* v___f_2898_, lean_object* v___x_2899_, lean_object* v_params_2900_, lean_object* v_body_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2907_ = lean_array_get_size(v_params_2900_);
v___x_2908_ = lean_array_get_borrowed(v___x_2893_, v___x_2894_, v_a_2895_);
v___x_2909_ = lean_nat_dec_eq(v___x_2907_, v___x_2908_);
if (v___x_2909_ == 0)
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
lean_dec_ref(v_body_2901_);
lean_dec_ref(v_params_2900_);
lean_dec_ref(v___f_2898_);
lean_dec(v_val_2897_);
lean_dec_ref(v_preDefs_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v___x_2894_);
v___x_2910_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__3);
v___x_2911_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6(v___x_2910_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
return v___x_2911_;
}
else
{
lean_object* v___f_2912_; uint8_t v___x_2913_; lean_object* v___x_2914_; 
v___f_2912_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_2912_, 0, v_preDefs_2896_);
lean_closure_set(v___f_2912_, 1, v___x_2894_);
lean_closure_set(v___f_2912_, 2, v_val_2897_);
lean_closure_set(v___f_2912_, 3, v_a_2895_);
lean_closure_set(v___f_2912_, 4, v_params_2900_);
lean_closure_set(v___f_2912_, 5, v___x_2907_);
v___x_2913_ = 0;
v___x_2914_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7(v_body_2901_, v___f_2912_, v___f_2898_, v___x_2913_, v___x_2909_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2921_ == 0)
{
lean_object* v_unused_2922_; 
v_unused_2922_ = lean_ctor_get(v___x_2914_, 0);
lean_dec(v_unused_2922_);
v___x_2916_ = v___x_2914_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_dec(v___x_2914_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v___x_2899_);
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2899_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
v_a_2923_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2914_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2914_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___boxed(lean_object* v___x_2931_, lean_object* v___x_2932_, lean_object* v_a_2933_, lean_object* v_preDefs_2934_, lean_object* v_val_2935_, lean_object* v___f_2936_, lean_object* v___x_2937_, lean_object* v_params_2938_, lean_object* v_body_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2(v___x_2931_, v___x_2932_, v_a_2933_, v_preDefs_2934_, v_val_2935_, v___f_2936_, v___x_2937_, v_params_2938_, v_body_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___x_2931_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg(lean_object* v_preDefs_2947_, lean_object* v___x_2948_, lean_object* v_val_2949_, lean_object* v_upperBound_2950_, lean_object* v_a_2951_, lean_object* v_b_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
uint8_t v___x_2958_; 
v___x_2958_ = lean_nat_dec_lt(v_a_2951_, v_upperBound_2950_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; 
lean_dec(v_a_2951_);
lean_dec(v_val_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_preDefs_2947_);
v___x_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2959_, 0, v_b_2952_);
return v___x_2959_;
}
else
{
lean_object* v___x_2960_; lean_object* v_value_2961_; lean_object* v___f_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___f_2965_; uint8_t v___x_2966_; lean_object* v___x_2967_; 
v___x_2960_ = lean_array_fget_borrowed(v_preDefs_2947_, v_a_2951_);
v_value_2961_ = lean_ctor_get(v___x_2960_, 7);
v___f_2962_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___closed__0));
v___x_2963_ = lean_unsigned_to_nat(0u);
v___x_2964_ = lean_box(0);
lean_inc(v_val_2949_);
lean_inc_ref(v_preDefs_2947_);
lean_inc(v_a_2951_);
lean_inc_ref(v___x_2948_);
v___f_2965_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_2965_, 0, v___x_2963_);
lean_closure_set(v___f_2965_, 1, v___x_2948_);
lean_closure_set(v___f_2965_, 2, v_a_2951_);
lean_closure_set(v___f_2965_, 3, v_preDefs_2947_);
lean_closure_set(v___f_2965_, 4, v_val_2949_);
lean_closure_set(v___f_2965_, 5, v___f_2962_);
lean_closure_set(v___f_2965_, 6, v___x_2964_);
v___x_2966_ = 0;
lean_inc_ref(v_value_2961_);
v___x_2967_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_2961_, v___f_2965_, v___x_2966_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
lean_dec_ref(v___x_2967_);
v___x_2968_ = lean_unsigned_to_nat(1u);
v___x_2969_ = lean_nat_add(v_a_2951_, v___x_2968_);
lean_dec(v_a_2951_);
v_a_2951_ = v___x_2969_;
v_b_2952_ = v___x_2964_;
goto _start;
}
else
{
lean_dec(v_a_2951_);
lean_dec(v_val_2949_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v_preDefs_2947_);
return v___x_2967_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___boxed(lean_object* v_preDefs_2971_, lean_object* v___x_2972_, lean_object* v_val_2973_, lean_object* v_upperBound_2974_, lean_object* v_a_2975_, lean_object* v_b_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg(v_preDefs_2971_, v___x_2972_, v_val_2973_, v_upperBound_2974_, v_a_2975_, v_b_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v_upperBound_2974_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(size_t v_sz_2983_, size_t v_i_2984_, lean_object* v_bs_2985_){
_start:
{
uint8_t v___x_2986_; 
v___x_2986_ = lean_usize_dec_lt(v_i_2984_, v_sz_2983_);
if (v___x_2986_ == 0)
{
return v_bs_2985_;
}
else
{
lean_object* v_v_2987_; lean_object* v___x_2988_; lean_object* v_bs_x27_2989_; lean_object* v___x_2990_; size_t v___x_2991_; size_t v___x_2992_; lean_object* v___x_2993_; 
v_v_2987_ = lean_array_uget(v_bs_2985_, v_i_2984_);
v___x_2988_ = lean_unsigned_to_nat(0u);
v_bs_x27_2989_ = lean_array_uset(v_bs_2985_, v_i_2984_, v___x_2988_);
v___x_2990_ = lean_array_get_size(v_v_2987_);
lean_dec(v_v_2987_);
v___x_2991_ = ((size_t)1ULL);
v___x_2992_ = lean_usize_add(v_i_2984_, v___x_2991_);
v___x_2993_ = lean_array_uset(v_bs_x27_2989_, v_i_2984_, v___x_2990_);
v_i_2984_ = v___x_2992_;
v_bs_2985_ = v___x_2993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1___boxed(lean_object* v_sz_2995_, lean_object* v_i_2996_, lean_object* v_bs_2997_){
_start:
{
size_t v_sz_boxed_2998_; size_t v_i_boxed_2999_; lean_object* v_res_3000_; 
v_sz_boxed_2998_ = lean_unbox_usize(v_sz_2995_);
lean_dec(v_sz_2995_);
v_i_boxed_2999_ = lean_unbox_usize(v_i_2996_);
lean_dec(v_i_2996_);
v_res_3000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_boxed_2998_, v_i_boxed_2999_, v_bs_2997_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(size_t v_sz_3001_, size_t v_i_3002_, lean_object* v_bs_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
uint8_t v___x_3009_; 
v___x_3009_ = lean_usize_dec_lt(v_i_3002_, v_sz_3001_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v_bs_3003_);
return v___x_3010_;
}
else
{
lean_object* v_v_3011_; lean_object* v_value_3012_; lean_object* v___x_3013_; 
v_v_3011_ = lean_array_uget_borrowed(v_bs_3003_, v_i_3002_);
v_value_3012_ = lean_ctor_get(v_v_3011_, 7);
lean_inc_ref(v_value_3012_);
v___x_3013_ = l_Lean_Elab_getParamRevDeps(v_value_3012_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; lean_object* v_bs_x27_3016_; size_t v___x_3017_; size_t v___x_3018_; lean_object* v___x_3019_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref(v___x_3013_);
v___x_3015_ = lean_unsigned_to_nat(0u);
v_bs_x27_3016_ = lean_array_uset(v_bs_3003_, v_i_3002_, v___x_3015_);
v___x_3017_ = ((size_t)1ULL);
v___x_3018_ = lean_usize_add(v_i_3002_, v___x_3017_);
v___x_3019_ = lean_array_uset(v_bs_x27_3016_, v_i_3002_, v_a_3014_);
v_i_3002_ = v___x_3018_;
v_bs_3003_ = v___x_3019_;
goto _start;
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref(v_bs_3003_);
v_a_3021_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3013_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3013_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0___boxed(lean_object* v_sz_3029_, lean_object* v_i_3030_, lean_object* v_bs_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
size_t v_sz_boxed_3037_; size_t v_i_boxed_3038_; lean_object* v_res_3039_; 
v_sz_boxed_3037_ = lean_unbox_usize(v_sz_3029_);
lean_dec(v_sz_3029_);
v_i_boxed_3038_ = lean_unbox_usize(v_i_3030_);
lean_dec(v_i_3030_);
v_res_3039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_boxed_3037_, v_i_boxed_3038_, v_bs_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
return v_res_3039_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3042_ = l_Lean_stringToMessageData(v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
size_t v_sz_3049_; size_t v___x_3050_; lean_object* v___x_3051_; 
v_sz_3049_ = lean_array_size(v_preDefs_3043_);
v___x_3050_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3043_);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3049_, v___x_3050_, v_preDefs_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; size_t v_sz_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc_n(v_a_3052_, 2);
lean_dec_ref(v___x_3051_);
v_sz_3053_ = lean_array_size(v_a_3052_);
v___x_3054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3053_, v___x_3050_, v_a_3052_);
v___x_3055_ = l_Lean_Elab_FixedParams_Info_init(v_a_3052_);
v___x_3056_ = lean_st_mk_ref(v___x_3055_);
v___x_3057_ = lean_st_ref_take(v___x_3056_);
v___x_3058_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3057_);
v___x_3059_ = lean_st_ref_set(v___x_3056_, v___x_3058_);
v___x_3060_ = lean_array_get_size(v_preDefs_3043_);
v___x_3061_ = lean_unsigned_to_nat(0u);
v___x_3062_ = lean_box(0);
lean_inc(v___x_3056_);
v___x_3063_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg(v_preDefs_3043_, v___x_3054_, v___x_3056_, v___x_3060_, v___x_3061_, v___x_3062_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3102_; 
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; 
v_unused_3103_ = lean_ctor_get(v___x_3063_, 0);
lean_dec(v_unused_3103_);
v___x_3065_ = v___x_3063_;
v_isShared_3066_ = v_isSharedCheck_3102_;
goto v_resetjp_3064_;
}
else
{
lean_dec(v___x_3063_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3102_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; lean_object* v_options_3068_; uint8_t v_hasTrace_3069_; 
v___x_3067_ = lean_st_ref_get(v___x_3056_);
lean_dec(v___x_3056_);
v_options_3068_ = lean_ctor_get(v_a_3046_, 2);
v_hasTrace_3069_ = lean_ctor_get_uint8(v_options_3068_, sizeof(void*)*1);
if (v_hasTrace_3069_ == 0)
{
lean_object* v___x_3071_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v___x_3067_);
v___x_3071_ = v___x_3065_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3067_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; 
v_inheritedTraceOptions_3073_ = lean_ctor_get(v_a_3046_, 13);
v___x_3074_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3));
v___x_3075_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__6);
v___x_3076_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3073_, v_options_3068_, v___x_3075_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3078_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v___x_3067_);
v___x_3078_ = v___x_3065_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3067_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
else
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
lean_del_object(v___x_3065_);
v___x_3080_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3067_);
v___x_3081_ = l_Lean_Elab_FixedParams_Info_format(v___x_3067_);
v___x_3082_ = l_Std_Format_indentD(v___x_3081_);
v___x_3083_ = l_Lean_MessageData_ofFormat(v___x_3082_);
v___x_3084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3080_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3074_, v___x_3084_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3092_ == 0)
{
lean_object* v_unused_3093_; 
v_unused_3093_ = lean_ctor_get(v___x_3085_, 0);
lean_dec(v_unused_3093_);
v___x_3087_ = v___x_3085_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_dec(v___x_3085_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3067_);
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3067_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec(v___x_3067_);
v_a_3094_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3085_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3085_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v___x_3056_);
v_a_3104_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3063_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3063_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref(v_preDefs_3043_);
v_a_3112_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3051_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3051_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v_upperBound_3127_, lean_object* v_val_3128_, lean_object* v_next_3129_, lean_object* v_params_3130_, lean_object* v___x_3131_, lean_object* v_val_3132_, lean_object* v_next_3133_, uint8_t v___x_3134_, lean_object* v_inst_3135_, lean_object* v_R_3136_, lean_object* v_a_3137_, uint8_t v_b_3138_, lean_object* v_c_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___redArg(v_upperBound_3127_, v_val_3128_, v_next_3129_, v_params_3130_, v___x_3131_, v_val_3132_, v_next_3133_, v___x_3134_, v_a_3137_, v_b_3138_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3146_ = _args[0];
lean_object* v_val_3147_ = _args[1];
lean_object* v_next_3148_ = _args[2];
lean_object* v_params_3149_ = _args[3];
lean_object* v___x_3150_ = _args[4];
lean_object* v_val_3151_ = _args[5];
lean_object* v_next_3152_ = _args[6];
lean_object* v___x_3153_ = _args[7];
lean_object* v_inst_3154_ = _args[8];
lean_object* v_R_3155_ = _args[9];
lean_object* v_a_3156_ = _args[10];
lean_object* v_b_3157_ = _args[11];
lean_object* v_c_3158_ = _args[12];
lean_object* v___y_3159_ = _args[13];
lean_object* v___y_3160_ = _args[14];
lean_object* v___y_3161_ = _args[15];
lean_object* v___y_3162_ = _args[16];
lean_object* v___y_3163_ = _args[17];
_start:
{
uint8_t v___x_45345__boxed_3164_; uint8_t v_b_boxed_3165_; lean_object* v_res_3166_; 
v___x_45345__boxed_3164_ = lean_unbox(v___x_3153_);
v_b_boxed_3165_ = lean_unbox(v_b_3157_);
v_res_3166_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__3(v_upperBound_3146_, v_val_3147_, v_next_3148_, v_params_3149_, v___x_3150_, v_val_3151_, v_next_3152_, v___x_45345__boxed_3164_, v_inst_3154_, v_R_3155_, v_a_3156_, v_b_boxed_3165_, v_c_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v_val_3151_);
lean_dec_ref(v_params_3149_);
lean_dec(v_next_3148_);
lean_dec(v_val_3147_);
lean_dec(v_upperBound_3146_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_val_3167_, lean_object* v_val_3168_, lean_object* v_upperBound_3169_, lean_object* v_args_3170_, lean_object* v_e_3171_, lean_object* v_next_3172_, lean_object* v_params_3173_, lean_object* v___x_3174_, uint8_t v___x_3175_, lean_object* v_inst_3176_, lean_object* v_R_3177_, lean_object* v_a_3178_, lean_object* v_b_3179_, lean_object* v_c_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_3167_, v_val_3168_, v_upperBound_3169_, v_args_3170_, v_e_3171_, v_next_3172_, v_params_3173_, v___x_3174_, v___x_3175_, v_a_3178_, v_b_3179_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_val_3187_ = _args[0];
lean_object* v_val_3188_ = _args[1];
lean_object* v_upperBound_3189_ = _args[2];
lean_object* v_args_3190_ = _args[3];
lean_object* v_e_3191_ = _args[4];
lean_object* v_next_3192_ = _args[5];
lean_object* v_params_3193_ = _args[6];
lean_object* v___x_3194_ = _args[7];
lean_object* v___x_3195_ = _args[8];
lean_object* v_inst_3196_ = _args[9];
lean_object* v_R_3197_ = _args[10];
lean_object* v_a_3198_ = _args[11];
lean_object* v_b_3199_ = _args[12];
lean_object* v_c_3200_ = _args[13];
lean_object* v___y_3201_ = _args[14];
lean_object* v___y_3202_ = _args[15];
lean_object* v___y_3203_ = _args[16];
lean_object* v___y_3204_ = _args[17];
lean_object* v___y_3205_ = _args[18];
_start:
{
uint8_t v___x_45380__boxed_3206_; lean_object* v_res_3207_; 
v___x_45380__boxed_3206_ = lean_unbox(v___x_3195_);
v_res_3207_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_val_3187_, v_val_3188_, v_upperBound_3189_, v_args_3190_, v_e_3191_, v_next_3192_, v_params_3193_, v___x_3194_, v___x_45380__boxed_3206_, v_inst_3196_, v_R_3197_, v_a_3198_, v_b_3199_, v_c_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___x_3194_);
lean_dec_ref(v_params_3193_);
lean_dec(v_next_3192_);
lean_dec_ref(v_args_3190_);
lean_dec(v_upperBound_3189_);
lean_dec(v_val_3187_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_preDefs_3208_, lean_object* v___x_3209_, lean_object* v_val_3210_, lean_object* v_upperBound_3211_, lean_object* v_inst_3212_, lean_object* v_R_3213_, lean_object* v_a_3214_, lean_object* v_b_3215_, lean_object* v_c_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg(v_preDefs_3208_, v___x_3209_, v_val_3210_, v_upperBound_3211_, v_a_3214_, v_b_3215_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_preDefs_3223_, lean_object* v___x_3224_, lean_object* v_val_3225_, lean_object* v_upperBound_3226_, lean_object* v_inst_3227_, lean_object* v_R_3228_, lean_object* v_a_3229_, lean_object* v_b_3230_, lean_object* v_c_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_preDefs_3223_, v___x_3224_, v_val_3225_, v_upperBound_3226_, v_inst_3227_, v_R_3228_, v_a_3229_, v_b_3230_, v_c_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v_upperBound_3226_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11(lean_object* v_upperBound_3238_, lean_object* v___x_3239_, lean_object* v_pre_3240_, lean_object* v_post_3241_, uint8_t v_usedLetOnly_3242_, uint8_t v_skipConstInApp_3243_, uint8_t v_skipInstances_3244_, lean_object* v___x_3245_, lean_object* v_inst_3246_, lean_object* v_R_3247_, lean_object* v_a_3248_, lean_object* v_b_3249_, lean_object* v_c_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___redArg(v_upperBound_3238_, v___x_3239_, v_pre_3240_, v_post_3241_, v_usedLetOnly_3242_, v_skipConstInApp_3243_, v_skipInstances_3244_, v_a_3248_, v_b_3249_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11___boxed(lean_object** _args){
lean_object* v_upperBound_3258_ = _args[0];
lean_object* v___x_3259_ = _args[1];
lean_object* v_pre_3260_ = _args[2];
lean_object* v_post_3261_ = _args[3];
lean_object* v_usedLetOnly_3262_ = _args[4];
lean_object* v_skipConstInApp_3263_ = _args[5];
lean_object* v_skipInstances_3264_ = _args[6];
lean_object* v___x_3265_ = _args[7];
lean_object* v_inst_3266_ = _args[8];
lean_object* v_R_3267_ = _args[9];
lean_object* v_a_3268_ = _args[10];
lean_object* v_b_3269_ = _args[11];
lean_object* v_c_3270_ = _args[12];
lean_object* v___y_3271_ = _args[13];
lean_object* v___y_3272_ = _args[14];
lean_object* v___y_3273_ = _args[15];
lean_object* v___y_3274_ = _args[16];
lean_object* v___y_3275_ = _args[17];
lean_object* v___y_3276_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3277_; uint8_t v_skipConstInApp_boxed_3278_; uint8_t v_skipInstances_boxed_3279_; lean_object* v_res_3280_; 
v_usedLetOnly_boxed_3277_ = lean_unbox(v_usedLetOnly_3262_);
v_skipConstInApp_boxed_3278_ = lean_unbox(v_skipConstInApp_3263_);
v_skipInstances_boxed_3279_ = lean_unbox(v_skipInstances_3264_);
v_res_3280_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__11(v_upperBound_3258_, v___x_3259_, v_pre_3260_, v_post_3261_, v_usedLetOnly_boxed_3277_, v_skipConstInApp_boxed_3278_, v_skipInstances_boxed_3279_, v___x_3265_, v_inst_3266_, v_R_3267_, v_a_3268_, v_b_3269_, v_c_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec(v___x_3265_);
lean_dec_ref(v___x_3259_);
lean_dec(v_upperBound_3258_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12(lean_object* v_00_u03b2_3281_, lean_object* v_m_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12___redArg(v_m_3282_, v_a_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3285_, lean_object* v_m_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12(v_00_u03b2_3285_, v_m_3286_, v_a_3287_);
lean_dec_ref(v_a_3287_);
lean_dec_ref(v_m_3286_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16(lean_object* v_00_u03b1_3289_, lean_object* v_name_3290_, uint8_t v_bi_3291_, lean_object* v_type_3292_, lean_object* v_k_3293_, uint8_t v_kind_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___redArg(v_name_3290_, v_bi_3291_, v_type_3292_, v_k_3293_, v_kind_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16___boxed(lean_object* v_00_u03b1_3302_, lean_object* v_name_3303_, lean_object* v_bi_3304_, lean_object* v_type_3305_, lean_object* v_k_3306_, lean_object* v_kind_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
uint8_t v_bi_boxed_3314_; uint8_t v_kind_boxed_3315_; lean_object* v_res_3316_; 
v_bi_boxed_3314_ = lean_unbox(v_bi_3304_);
v_kind_boxed_3315_ = lean_unbox(v_kind_3307_);
v_res_3316_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__13_spec__16(v_00_u03b1_3302_, v_name_3303_, v_bi_boxed_3314_, v_type_3305_, v_k_3306_, v_kind_boxed_3315_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19(lean_object* v_00_u03b1_3317_, lean_object* v_name_3318_, lean_object* v_type_3319_, lean_object* v_val_3320_, lean_object* v_k_3321_, uint8_t v_nondep_3322_, uint8_t v_kind_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19___redArg(v_name_3318_, v_type_3319_, v_val_3320_, v_k_3321_, v_nondep_3322_, v_kind_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19___boxed(lean_object* v_00_u03b1_3331_, lean_object* v_name_3332_, lean_object* v_type_3333_, lean_object* v_val_3334_, lean_object* v_k_3335_, lean_object* v_nondep_3336_, lean_object* v_kind_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
uint8_t v_nondep_boxed_3344_; uint8_t v_kind_boxed_3345_; lean_object* v_res_3346_; 
v_nondep_boxed_3344_ = lean_unbox(v_nondep_3336_);
v_kind_boxed_3345_ = lean_unbox(v_kind_3337_);
v_res_3346_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__15_spec__19(v_00_u03b1_3331_, v_name_3332_, v_type_3333_, v_val_3334_, v_k_3335_, v_nondep_boxed_3344_, v_kind_boxed_3345_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22(lean_object* v_00_u03b1_3347_, lean_object* v_ref_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___redArg(v_ref_3348_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22___boxed(lean_object* v_00_u03b1_3355_, lean_object* v_ref_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17_spec__22(v_00_u03b1_3355_, v_ref_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17(lean_object* v_00_u03b1_3363_, lean_object* v_x_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___redArg(v_x_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17___boxed(lean_object* v_00_u03b1_3372_, lean_object* v_x_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__17(v_00_u03b1_3372_, v_x_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18(lean_object* v_00_u03b2_3381_, lean_object* v_m_3382_, lean_object* v_a_3383_, lean_object* v_b_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18___redArg(v_m_3382_, v_a_3383_, v_b_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14(lean_object* v_00_u03b2_3386_, lean_object* v_a_3387_, lean_object* v_x_3388_){
_start:
{
lean_object* v___x_3389_; 
v___x_3389_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14___redArg(v_a_3387_, v_x_3388_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14___boxed(lean_object* v_00_u03b2_3390_, lean_object* v_a_3391_, lean_object* v_x_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__12_spec__14(v_00_u03b2_3390_, v_a_3391_, v_x_3392_);
lean_dec(v_x_3392_);
lean_dec_ref(v_a_3391_);
return v_res_3393_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24(lean_object* v_00_u03b2_3394_, lean_object* v_a_3395_, lean_object* v_x_3396_){
_start:
{
uint8_t v___x_3397_; 
v___x_3397_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24___redArg(v_a_3395_, v_x_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24___boxed(lean_object* v_00_u03b2_3398_, lean_object* v_a_3399_, lean_object* v_x_3400_){
_start:
{
uint8_t v_res_3401_; lean_object* v_r_3402_; 
v_res_3401_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__24(v_00_u03b2_3398_, v_a_3399_, v_x_3400_);
lean_dec(v_x_3400_);
lean_dec_ref(v_a_3399_);
v_r_3402_ = lean_box(v_res_3401_);
return v_r_3402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25(lean_object* v_00_u03b2_3403_, lean_object* v_data_3404_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25___redArg(v_data_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__26(lean_object* v_00_u03b2_3406_, lean_object* v_a_3407_, lean_object* v_b_3408_, lean_object* v_x_3409_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__26___redArg(v_a_3407_, v_b_3408_, v_x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26(lean_object* v_00_u03b2_3411_, lean_object* v_i_3412_, lean_object* v_source_3413_, lean_object* v_target_3414_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26___redArg(v_i_3412_, v_source_3413_, v_target_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26_spec__27(lean_object* v_00_u03b2_3416_, lean_object* v_x_3417_, lean_object* v_x_3418_){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__7_spec__8_spec__18_spec__25_spec__26_spec__27___redArg(v_x_3417_, v_x_3418_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3433_, lean_object* v_x_3434_){
_start:
{
if (lean_obj_tag(v_x_3433_) == 0)
{
lean_object* v___x_3435_; 
v___x_3435_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3435_;
}
else
{
lean_object* v_val_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3447_; 
v_val_3436_ = lean_ctor_get(v_x_3433_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_x_3433_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3438_ = v_x_3433_;
v_isShared_3439_ = v_isSharedCheck_3447_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_val_3436_);
lean_dec(v_x_3433_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3447_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3440_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3441_ = l_Nat_reprFast(v_val_3436_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set_tag(v___x_3438_, 3);
lean_ctor_set(v___x_3438_, 0, v___x_3441_);
v___x_3443_ = v___x_3438_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3440_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v___x_3445_ = l_Repr_addAppParen(v___x_3444_, v_x_3434_);
return v___x_3445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3448_, lean_object* v_x_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3448_, v_x_3449_);
lean_dec(v_x_3449_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3451_, lean_object* v_x_3452_, lean_object* v_x_3453_){
_start:
{
if (lean_obj_tag(v_x_3453_) == 0)
{
lean_dec(v_x_3451_);
return v_x_3452_;
}
else
{
lean_object* v_head_3454_; lean_object* v_tail_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3466_; 
v_head_3454_ = lean_ctor_get(v_x_3453_, 0);
v_tail_3455_ = lean_ctor_get(v_x_3453_, 1);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_x_3453_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3457_ = v_x_3453_;
v_isShared_3458_ = v_isSharedCheck_3466_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_tail_3455_);
lean_inc(v_head_3454_);
lean_dec(v_x_3453_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3466_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
lean_inc(v_x_3451_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set_tag(v___x_3457_, 5);
lean_ctor_set(v___x_3457_, 1, v_x_3451_);
lean_ctor_set(v___x_3457_, 0, v_x_3452_);
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_x_3452_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_x_3451_);
v___x_3460_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3461_ = lean_unsigned_to_nat(0u);
v___x_3462_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3454_, v___x_3461_);
v___x_3463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3460_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
v_x_3452_ = v___x_3463_;
v_x_3453_ = v_tail_3455_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3467_, lean_object* v_x_3468_, lean_object* v_x_3469_){
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
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3477_ = lean_unsigned_to_nat(0u);
v___x_3478_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3470_, v___x_3477_);
v___x_3479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3476_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
v___x_3480_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3467_, v___x_3479_, v_tail_3471_);
return v___x_3480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3483_){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = lean_unsigned_to_nat(0u);
v___x_3485_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3483_, v___x_3484_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3486_, lean_object* v_x_3487_){
_start:
{
if (lean_obj_tag(v_x_3486_) == 0)
{
lean_object* v___x_3488_; 
lean_dec(v_x_3487_);
v___x_3488_ = lean_box(0);
return v___x_3488_;
}
else
{
lean_object* v_tail_3489_; 
v_tail_3489_ = lean_ctor_get(v_x_3486_, 1);
if (lean_obj_tag(v_tail_3489_) == 0)
{
lean_object* v_head_3490_; lean_object* v___x_3491_; 
lean_dec(v_x_3487_);
v_head_3490_ = lean_ctor_get(v_x_3486_, 0);
lean_inc(v_head_3490_);
lean_dec_ref(v_x_3486_);
v___x_3491_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3490_);
return v___x_3491_;
}
else
{
lean_object* v_head_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
lean_inc(v_tail_3489_);
v_head_3492_ = lean_ctor_get(v_x_3486_, 0);
lean_inc(v_head_3492_);
lean_dec_ref(v_x_3486_);
v___x_3493_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3492_);
v___x_3494_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3487_, v___x_3493_, v_tail_3489_);
return v___x_3494_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3503_ = lean_string_length(v___x_3502_);
return v___x_3503_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3505_ = lean_nat_to_int(v___x_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3511_){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
v___x_3512_ = lean_array_get_size(v_xs_3511_);
v___x_3513_ = lean_unsigned_to_nat(0u);
v___x_3514_ = lean_nat_dec_eq(v___x_3512_, v___x_3513_);
if (v___x_3514_ == 0)
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3515_ = lean_array_to_list(v_xs_3511_);
v___x_3516_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3517_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3515_, v___x_3516_);
v___x_3518_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3519_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
lean_ctor_set(v___x_3520_, 1, v___x_3517_);
v___x_3521_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3518_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v___x_3524_ = l_Std_Format_fill(v___x_3523_);
return v___x_3524_;
}
else
{
lean_object* v___x_3525_; 
lean_dec_ref(v_xs_3511_);
v___x_3525_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3525_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3526_, lean_object* v_x_3527_, lean_object* v_x_3528_){
_start:
{
if (lean_obj_tag(v_x_3528_) == 0)
{
lean_dec(v_x_3526_);
return v_x_3527_;
}
else
{
lean_object* v_head_3529_; lean_object* v_tail_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3540_; 
v_head_3529_ = lean_ctor_get(v_x_3528_, 0);
v_tail_3530_ = lean_ctor_get(v_x_3528_, 1);
v_isSharedCheck_3540_ = !lean_is_exclusive(v_x_3528_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3532_ = v_x_3528_;
v_isShared_3533_ = v_isSharedCheck_3540_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_tail_3530_);
lean_inc(v_head_3529_);
lean_dec(v_x_3528_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3540_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
lean_inc(v_x_3526_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set_tag(v___x_3532_, 5);
lean_ctor_set(v___x_3532_, 1, v_x_3526_);
lean_ctor_set(v___x_3532_, 0, v_x_3527_);
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_x_3527_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_x_3526_);
v___x_3535_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3529_);
v___x_3537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3535_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
v_x_3527_ = v___x_3537_;
v_x_3528_ = v_tail_3530_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3541_, lean_object* v_x_3542_){
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
lean_dec_ref(v_x_3541_);
v___x_3546_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3545_);
return v___x_3546_;
}
else
{
lean_object* v_head_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
lean_inc(v_tail_3544_);
v_head_3547_ = lean_ctor_get(v_x_3541_, 0);
lean_inc(v_head_3547_);
lean_dec_ref(v_x_3541_);
v___x_3548_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3547_);
v___x_3549_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3542_, v___x_3548_, v_tail_3544_);
return v___x_3549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3550_){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; 
v___x_3551_ = lean_array_get_size(v_xs_3550_);
v___x_3552_ = lean_unsigned_to_nat(0u);
v___x_3553_ = lean_nat_dec_eq(v___x_3551_, v___x_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3554_ = lean_array_to_list(v_xs_3550_);
v___x_3555_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3556_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3554_, v___x_3555_);
v___x_3557_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3558_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
lean_ctor_set(v___x_3559_, 1, v___x_3556_);
v___x_3560_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3559_);
lean_ctor_set(v___x_3561_, 1, v___x_3560_);
v___x_3562_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3557_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v___x_3563_ = l_Std_Format_fill(v___x_3562_);
return v___x_3563_;
}
else
{
lean_object* v___x_3564_; 
lean_dec_ref(v_xs_3550_);
v___x_3564_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3564_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3565_, lean_object* v_x_3566_, lean_object* v_x_3567_){
_start:
{
if (lean_obj_tag(v_x_3567_) == 0)
{
lean_dec(v_x_3565_);
return v_x_3566_;
}
else
{
lean_object* v_head_3568_; lean_object* v_tail_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3580_; 
v_head_3568_ = lean_ctor_get(v_x_3567_, 0);
v_tail_3569_ = lean_ctor_get(v_x_3567_, 1);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_x_3567_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3571_ = v_x_3567_;
v_isShared_3572_ = v_isSharedCheck_3580_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_tail_3569_);
lean_inc(v_head_3568_);
lean_dec(v_x_3567_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3580_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
lean_inc(v_x_3565_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set_tag(v___x_3571_, 5);
lean_ctor_set(v___x_3571_, 1, v_x_3565_);
lean_ctor_set(v___x_3571_, 0, v_x_3566_);
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_x_3566_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_x_3565_);
v___x_3574_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3575_ = l_Nat_reprFast(v_head_3568_);
v___x_3576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
v___x_3577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3574_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
v_x_3566_ = v___x_3577_;
v_x_3567_ = v_tail_3569_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3581_, lean_object* v_x_3582_, lean_object* v_x_3583_){
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
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3591_ = l_Nat_reprFast(v_head_3584_);
v___x_3592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
v___x_3593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3590_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v___x_3594_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3581_, v___x_3593_, v_tail_3585_);
return v___x_3594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3597_){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = l_Nat_reprFast(v___y_3597_);
v___x_3599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3600_, lean_object* v_x_3601_){
_start:
{
if (lean_obj_tag(v_x_3600_) == 0)
{
lean_object* v___x_3602_; 
lean_dec(v_x_3601_);
v___x_3602_ = lean_box(0);
return v___x_3602_;
}
else
{
lean_object* v_tail_3603_; 
v_tail_3603_ = lean_ctor_get(v_x_3600_, 1);
if (lean_obj_tag(v_tail_3603_) == 0)
{
lean_object* v_head_3604_; lean_object* v___x_3605_; 
lean_dec(v_x_3601_);
v_head_3604_ = lean_ctor_get(v_x_3600_, 0);
lean_inc(v_head_3604_);
lean_dec_ref(v_x_3600_);
v___x_3605_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3604_);
return v___x_3605_;
}
else
{
lean_object* v_head_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
lean_inc(v_tail_3603_);
v_head_3606_ = lean_ctor_get(v_x_3600_, 0);
lean_inc(v_head_3606_);
lean_dec_ref(v_x_3600_);
v___x_3607_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3606_);
v___x_3608_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3601_, v___x_3607_, v_tail_3603_);
return v___x_3608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3609_){
_start:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3610_ = lean_array_get_size(v_xs_3609_);
v___x_3611_ = lean_unsigned_to_nat(0u);
v___x_3612_ = lean_nat_dec_eq(v___x_3610_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3613_ = lean_array_to_list(v_xs_3609_);
v___x_3614_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3615_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3613_, v___x_3614_);
v___x_3616_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3617_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
lean_ctor_set(v___x_3618_, 1, v___x_3615_);
v___x_3619_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3616_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = l_Std_Format_fill(v___x_3621_);
return v___x_3622_;
}
else
{
lean_object* v___x_3623_; 
lean_dec_ref(v_xs_3609_);
v___x_3623_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3623_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3624_, lean_object* v_x_3625_, lean_object* v_x_3626_){
_start:
{
if (lean_obj_tag(v_x_3626_) == 0)
{
lean_dec(v_x_3624_);
return v_x_3625_;
}
else
{
lean_object* v_head_3627_; lean_object* v_tail_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3638_; 
v_head_3627_ = lean_ctor_get(v_x_3626_, 0);
v_tail_3628_ = lean_ctor_get(v_x_3626_, 1);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_x_3626_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3630_ = v_x_3626_;
v_isShared_3631_ = v_isSharedCheck_3638_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_tail_3628_);
lean_inc(v_head_3627_);
lean_dec(v_x_3626_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3638_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
lean_inc(v_x_3624_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 5);
lean_ctor_set(v___x_3630_, 1, v_x_3624_);
lean_ctor_set(v___x_3630_, 0, v_x_3625_);
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_x_3625_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_x_3624_);
v___x_3633_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3627_);
v___x_3635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3633_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v_x_3625_ = v___x_3635_;
v_x_3626_ = v_tail_3628_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3639_, lean_object* v_x_3640_){
_start:
{
if (lean_obj_tag(v_x_3639_) == 0)
{
lean_object* v___x_3641_; 
lean_dec(v_x_3640_);
v___x_3641_ = lean_box(0);
return v___x_3641_;
}
else
{
lean_object* v_tail_3642_; 
v_tail_3642_ = lean_ctor_get(v_x_3639_, 1);
if (lean_obj_tag(v_tail_3642_) == 0)
{
lean_object* v_head_3643_; lean_object* v___x_3644_; 
lean_dec(v_x_3640_);
v_head_3643_ = lean_ctor_get(v_x_3639_, 0);
lean_inc(v_head_3643_);
lean_dec_ref(v_x_3639_);
v___x_3644_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3643_);
return v___x_3644_;
}
else
{
lean_object* v_head_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
lean_inc(v_tail_3642_);
v_head_3645_ = lean_ctor_get(v_x_3639_, 0);
lean_inc(v_head_3645_);
lean_dec_ref(v_x_3639_);
v___x_3646_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3645_);
v___x_3647_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3640_, v___x_3646_, v_tail_3642_);
return v___x_3647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3648_){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; uint8_t v___x_3651_; 
v___x_3649_ = lean_array_get_size(v_xs_3648_);
v___x_3650_ = lean_unsigned_to_nat(0u);
v___x_3651_ = lean_nat_dec_eq(v___x_3649_, v___x_3650_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3652_ = lean_array_to_list(v_xs_3648_);
v___x_3653_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3654_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3652_, v___x_3653_);
v___x_3655_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3656_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
lean_ctor_set(v___x_3657_, 1, v___x_3654_);
v___x_3658_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3655_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = l_Std_Format_fill(v___x_3660_);
return v___x_3661_;
}
else
{
lean_object* v___x_3662_; 
lean_dec_ref(v_xs_3648_);
v___x_3662_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3662_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3663_, lean_object* v_x_3664_, lean_object* v_x_3665_){
_start:
{
if (lean_obj_tag(v_x_3665_) == 0)
{
lean_dec(v_x_3663_);
return v_x_3664_;
}
else
{
lean_object* v_head_3666_; lean_object* v_tail_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3677_; 
v_head_3666_ = lean_ctor_get(v_x_3665_, 0);
v_tail_3667_ = lean_ctor_get(v_x_3665_, 1);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_x_3665_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3669_ = v_x_3665_;
v_isShared_3670_ = v_isSharedCheck_3677_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_tail_3667_);
lean_inc(v_head_3666_);
lean_dec(v_x_3665_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3677_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
lean_inc(v_x_3663_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set_tag(v___x_3669_, 5);
lean_ctor_set(v___x_3669_, 1, v_x_3663_);
lean_ctor_set(v___x_3669_, 0, v_x_3664_);
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_x_3664_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_x_3663_);
v___x_3672_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3666_);
v___x_3674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3672_);
lean_ctor_set(v___x_3674_, 1, v___x_3673_);
v_x_3664_ = v___x_3674_;
v_x_3665_ = v_tail_3667_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3678_, lean_object* v_x_3679_){
_start:
{
if (lean_obj_tag(v_x_3678_) == 0)
{
lean_object* v___x_3680_; 
lean_dec(v_x_3679_);
v___x_3680_ = lean_box(0);
return v___x_3680_;
}
else
{
lean_object* v_tail_3681_; 
v_tail_3681_ = lean_ctor_get(v_x_3678_, 1);
if (lean_obj_tag(v_tail_3681_) == 0)
{
lean_object* v_head_3682_; lean_object* v___x_3683_; 
lean_dec(v_x_3679_);
v_head_3682_ = lean_ctor_get(v_x_3678_, 0);
lean_inc(v_head_3682_);
lean_dec_ref(v_x_3678_);
v___x_3683_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3682_);
return v___x_3683_;
}
else
{
lean_object* v_head_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
lean_inc(v_tail_3681_);
v_head_3684_ = lean_ctor_get(v_x_3678_, 0);
lean_inc(v_head_3684_);
lean_dec_ref(v_x_3678_);
v___x_3685_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3684_);
v___x_3686_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3679_, v___x_3685_, v_tail_3681_);
return v___x_3686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3687_){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; 
v___x_3688_ = lean_array_get_size(v_xs_3687_);
v___x_3689_ = lean_unsigned_to_nat(0u);
v___x_3690_ = lean_nat_dec_eq(v___x_3688_, v___x_3689_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3691_ = lean_array_to_list(v_xs_3687_);
v___x_3692_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3693_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3691_, v___x_3692_);
v___x_3694_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3695_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3695_);
lean_ctor_set(v___x_3696_, 1, v___x_3693_);
v___x_3697_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3696_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3694_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
v___x_3700_ = l_Std_Format_fill(v___x_3699_);
return v___x_3700_;
}
else
{
lean_object* v___x_3701_; 
lean_dec_ref(v_xs_3687_);
v___x_3701_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3701_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3715_ = lean_unsigned_to_nat(12u);
v___x_3716_ = lean_nat_to_int(v___x_3715_);
return v___x_3716_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = lean_unsigned_to_nat(9u);
v___x_3721_ = lean_nat_to_int(v___x_3720_);
return v___x_3721_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = lean_unsigned_to_nat(11u);
v___x_3726_ = lean_nat_to_int(v___x_3725_);
return v___x_3726_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3729_ = lean_string_length(v___x_3728_);
return v___x_3729_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3731_ = lean_nat_to_int(v___x_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3736_){
_start:
{
lean_object* v_numFixed_3737_; lean_object* v_perms_3738_; lean_object* v_revDeps_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; uint8_t v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v_numFixed_3737_ = lean_ctor_get(v_x_3736_, 0);
lean_inc(v_numFixed_3737_);
v_perms_3738_ = lean_ctor_get(v_x_3736_, 1);
lean_inc_ref(v_perms_3738_);
v_revDeps_3739_ = lean_ctor_get(v_x_3736_, 2);
lean_inc_ref(v_revDeps_3739_);
lean_dec_ref(v_x_3736_);
v___x_3740_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3741_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3742_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3743_ = l_Nat_reprFast(v_numFixed_3737_);
v___x_3744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
v___x_3745_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3742_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = 0;
v___x_3747_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3747_, 0, v___x_3745_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*1, v___x_3746_);
v___x_3748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3741_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = lean_box(1);
v___x_3752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3752_);
lean_ctor_set(v___x_3754_, 1, v___x_3753_);
v___x_3755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
lean_ctor_set(v___x_3755_, 1, v___x_3740_);
v___x_3756_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3757_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3738_);
v___x_3758_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3756_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
v___x_3759_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
lean_ctor_set_uint8(v___x_3759_, sizeof(void*)*1, v___x_3746_);
v___x_3760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3755_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
lean_ctor_set(v___x_3761_, 1, v___x_3749_);
v___x_3762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
lean_ctor_set(v___x_3762_, 1, v___x_3751_);
v___x_3763_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
lean_ctor_set(v___x_3765_, 1, v___x_3740_);
v___x_3766_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3767_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3739_);
v___x_3768_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3766_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
lean_ctor_set_uint8(v___x_3769_, sizeof(void*)*1, v___x_3746_);
v___x_3770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3765_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3772_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
lean_ctor_set(v___x_3773_, 1, v___x_3770_);
v___x_3774_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3773_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3771_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
v___x_3777_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
lean_ctor_set_uint8(v___x_3777_, sizeof(void*)*1, v___x_3746_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3778_, lean_object* v_prec_3779_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3778_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3781_, lean_object* v_prec_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3781_, v_prec_3782_);
lean_dec(v_prec_3782_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v___f_3792_; lean_object* v___x_5797__overap_3793_; lean_object* v___x_3794_; 
v___f_3792_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_5797__overap_3793_ = lean_panic_fn_borrowed(v___f_3792_, v_msg_3786_);
lean_inc(v___y_3790_);
lean_inc_ref(v___y_3789_);
lean_inc(v___y_3788_);
lean_inc_ref(v___y_3787_);
v___x_3794_ = lean_apply_5(v___x_5797__overap_3793_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, lean_box(0));
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___f_3808_; lean_object* v___x_5807__overap_3809_; lean_object* v___x_3810_; 
v___f_3808_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_5807__overap_3809_ = lean_panic_fn_borrowed(v___f_3808_, v_msg_3802_);
lean_inc(v___y_3806_);
lean_inc_ref(v___y_3805_);
lean_inc(v___y_3804_);
lean_inc_ref(v___y_3803_);
v___x_3810_ = lean_apply_5(v___x_5807__overap_3809_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, lean_box(0));
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v___f_3824_; lean_object* v___x_5817__overap_3825_; lean_object* v___x_3826_; 
v___f_3824_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_5817__overap_3825_ = lean_panic_fn_borrowed(v___f_3824_, v_msg_3818_);
lean_inc(v___y_3822_);
lean_inc_ref(v___y_3821_);
lean_inc(v___y_3820_);
lean_inc_ref(v___y_3819_);
v___x_3826_ = lean_apply_5(v___x_5817__overap_3825_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, lean_box(0));
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
return v_res_3833_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3837_ = lean_unsigned_to_nat(12u);
v___x_3838_ = lean_unsigned_to_nat(294u);
v___x_3839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3840_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_3841_ = l_mkPanicMessageWithDecl(v___x_3840_, v___x_3839_, v___x_3838_, v___x_3837_, v___x_3836_);
return v___x_3841_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3844_ = lean_unsigned_to_nat(12u);
v___x_3845_ = lean_unsigned_to_nat(297u);
v___x_3846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3847_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_3848_ = l_mkPanicMessageWithDecl(v___x_3847_, v___x_3846_, v___x_3845_, v___x_3844_, v___x_3843_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3849_, lean_object* v_as_3850_, size_t v_sz_3851_, size_t v_i_3852_, lean_object* v_b_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_a_3860_; uint8_t v___x_3864_; 
v___x_3864_ = lean_usize_dec_lt(v_i_3852_, v_sz_3851_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3865_, 0, v_b_3853_);
return v___x_3865_;
}
else
{
lean_object* v_a_3866_; 
v_a_3866_ = lean_array_uget_borrowed(v_as_3850_, v_i_3852_);
if (lean_obj_tag(v_a_3866_) == 1)
{
lean_object* v_val_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v_val_3867_ = lean_ctor_get(v_a_3866_, 0);
v___x_3868_ = lean_unsigned_to_nat(0u);
v___x_3869_ = lean_box(0);
v___x_3870_ = lean_array_get_borrowed(v___x_3869_, v_val_3867_, v___x_3868_);
if (lean_obj_tag(v___x_3870_) == 1)
{
lean_object* v_val_3871_; lean_object* v___x_3872_; 
v_val_3871_ = lean_ctor_get(v___x_3870_, 0);
v___x_3872_ = lean_array_get_borrowed(v___x_3869_, v___x_3849_, v_val_3871_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
lean_dec_ref(v_b_3853_);
v___x_3873_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3874_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3873_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3884_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3877_ = v___x_3874_;
v_isShared_3878_ = v_isSharedCheck_3884_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3884_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
if (lean_obj_tag(v_a_3875_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3881_; 
v_a_3879_ = lean_ctor_get(v_a_3875_, 0);
lean_inc(v_a_3879_);
lean_dec_ref(v_a_3875_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v_a_3879_);
v___x_3881_ = v___x_3877_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3879_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
else
{
lean_object* v_a_3883_; 
lean_del_object(v___x_3877_);
v_a_3883_ = lean_ctor_get(v_a_3875_, 0);
lean_inc(v_a_3883_);
lean_dec_ref(v_a_3875_);
v_a_3860_ = v_a_3883_;
goto v___jp_3859_;
}
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
v_a_3885_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3874_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3874_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
else
{
lean_object* v___x_3893_; 
lean_inc_ref(v___x_3872_);
v___x_3893_ = lean_array_push(v_b_3853_, v___x_3872_);
v_a_3860_ = v___x_3893_;
goto v___jp_3859_;
}
}
else
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3895_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6(v___x_3894_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_dec_ref(v___x_3895_);
v_a_3860_ = v_b_3853_;
goto v___jp_3859_;
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_dec_ref(v_b_3853_);
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3895_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3895_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
}
else
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = lean_box(0);
v___x_3905_ = lean_array_push(v_b_3853_, v___x_3904_);
v_a_3860_ = v___x_3905_;
goto v___jp_3859_;
}
}
v___jp_3859_:
{
size_t v___x_3861_; size_t v___x_3862_; 
v___x_3861_ = ((size_t)1ULL);
v___x_3862_ = lean_usize_add(v_i_3852_, v___x_3861_);
v_i_3852_ = v___x_3862_;
v_b_3853_ = v_a_3860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3906_, lean_object* v_as_3907_, lean_object* v_sz_3908_, lean_object* v_i_3909_, lean_object* v_b_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
size_t v_sz_boxed_3916_; size_t v_i_boxed_3917_; lean_object* v_res_3918_; 
v_sz_boxed_3916_ = lean_unbox_usize(v_sz_3908_);
lean_dec(v_sz_3908_);
v_i_boxed_3917_ = lean_unbox_usize(v_i_3909_);
lean_dec(v_i_3909_);
v_res_3918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3906_, v_as_3907_, v_sz_boxed_3916_, v_i_boxed_3917_, v_b_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec_ref(v_as_3907_);
lean_dec_ref(v___x_3906_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3921_, lean_object* v___x_3922_, lean_object* v___x_3923_, lean_object* v_a_3924_, lean_object* v_b_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
uint8_t v___x_3931_; 
v___x_3931_ = lean_nat_dec_lt(v_a_3924_, v_upperBound_3921_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; 
lean_dec(v_a_3924_);
v___x_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3932_, 0, v_b_3925_);
return v___x_3932_;
}
else
{
lean_object* v___x_3933_; lean_object* v___x_3934_; size_t v_sz_3935_; size_t v___x_3936_; lean_object* v___x_3937_; 
v___x_3933_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3934_ = lean_array_fget_borrowed(v___x_3922_, v_a_3924_);
v_sz_3935_ = lean_array_size(v___x_3934_);
v___x_3936_ = ((size_t)0ULL);
v___x_3937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3923_, v___x_3934_, v_sz_3935_, v___x_3936_, v___x_3933_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref(v___x_3937_);
v___x_3939_ = lean_array_push(v_b_3925_, v_a_3938_);
v___x_3940_ = lean_unsigned_to_nat(1u);
v___x_3941_ = lean_nat_add(v_a_3924_, v___x_3940_);
lean_dec(v_a_3924_);
v_a_3924_ = v___x_3941_;
v_b_3925_ = v___x_3939_;
goto _start;
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec_ref(v_b_3925_);
lean_dec(v_a_3924_);
v_a_3943_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3937_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3937_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3951_, lean_object* v___x_3952_, lean_object* v___x_3953_, lean_object* v_a_3954_, lean_object* v_b_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3951_, v___x_3952_, v___x_3953_, v_a_3954_, v_b_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec_ref(v___x_3953_);
lean_dec_ref(v___x_3952_);
lean_dec(v_upperBound_3951_);
return v_res_3961_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3963_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3964_ = lean_unsigned_to_nat(8u);
v___x_3965_ = lean_unsigned_to_nat(281u);
v___x_3966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3967_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_3968_ = l_mkPanicMessageWithDecl(v___x_3967_, v___x_3966_, v___x_3965_, v___x_3964_, v___x_3963_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3969_, lean_object* v_a_3970_, lean_object* v_b_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_a_3978_; uint8_t v___x_3982_; 
v___x_3982_ = lean_nat_dec_lt(v_a_3970_, v_upperBound_3969_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; 
lean_dec(v_a_3970_);
v___x_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3983_, 0, v_b_3971_);
return v___x_3983_;
}
else
{
lean_object* v_snd_3984_; lean_object* v_snd_3985_; lean_object* v_snd_3986_; lean_object* v_fst_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_4111_; 
v_snd_3984_ = lean_ctor_get(v_b_3971_, 1);
lean_inc(v_snd_3984_);
v_snd_3985_ = lean_ctor_get(v_snd_3984_, 1);
lean_inc(v_snd_3985_);
v_snd_3986_ = lean_ctor_get(v_snd_3985_, 1);
lean_inc(v_snd_3986_);
v_fst_3987_ = lean_ctor_get(v_b_3971_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v_b_3971_);
if (v_isSharedCheck_4111_ == 0)
{
lean_object* v_unused_4112_; 
v_unused_4112_ = lean_ctor_get(v_b_3971_, 1);
lean_dec(v_unused_4112_);
v___x_3989_ = v_b_3971_;
v_isShared_3990_ = v_isSharedCheck_4111_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_fst_3987_);
lean_dec(v_b_3971_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_4111_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v_fst_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4109_; 
v_fst_3991_ = lean_ctor_get(v_snd_3984_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v_snd_3984_);
if (v_isSharedCheck_4109_ == 0)
{
lean_object* v_unused_4110_; 
v_unused_4110_ = lean_ctor_get(v_snd_3984_, 1);
lean_dec(v_unused_4110_);
v___x_3993_ = v_snd_3984_;
v_isShared_3994_ = v_isSharedCheck_4109_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_fst_3991_);
lean_dec(v_snd_3984_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4109_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v_fst_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4107_; 
v_fst_3995_ = lean_ctor_get(v_snd_3985_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v_snd_3985_);
if (v_isSharedCheck_4107_ == 0)
{
lean_object* v_unused_4108_; 
v_unused_4108_ = lean_ctor_get(v_snd_3985_, 1);
lean_dec(v_unused_4108_);
v___x_3997_ = v_snd_3985_;
v_isShared_3998_ = v_isSharedCheck_4107_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_fst_3995_);
lean_dec(v_snd_3985_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4107_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v_array_3999_; lean_object* v_start_4000_; lean_object* v_stop_4001_; uint8_t v___x_4002_; 
v_array_3999_ = lean_ctor_get(v_snd_3986_, 0);
v_start_4000_ = lean_ctor_get(v_snd_3986_, 1);
v_stop_4001_ = lean_ctor_get(v_snd_3986_, 2);
v___x_4002_ = lean_nat_dec_lt(v_start_4000_, v_stop_4001_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4004_; 
lean_dec(v_a_3970_);
if (v_isShared_3998_ == 0)
{
v___x_4004_ = v___x_3997_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_fst_3995_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_snd_3986_);
v___x_4004_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
lean_object* v___x_4006_; 
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 1, v___x_4004_);
v___x_4006_ = v___x_3993_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_fst_3991_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v___x_4004_);
v___x_4006_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
lean_object* v___x_4008_; 
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 1, v___x_4006_);
v___x_4008_ = v___x_3989_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_fst_3987_);
lean_ctor_set(v_reuseFailAlloc_4010_, 1, v___x_4006_);
v___x_4008_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
lean_object* v___x_4009_; 
v___x_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
return v___x_4009_;
}
}
}
}
else
{
lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4103_; 
lean_inc(v_stop_4001_);
lean_inc(v_start_4000_);
lean_inc_ref(v_array_3999_);
v_isSharedCheck_4103_ = !lean_is_exclusive(v_snd_3986_);
if (v_isSharedCheck_4103_ == 0)
{
lean_object* v_unused_4104_; lean_object* v_unused_4105_; lean_object* v_unused_4106_; 
v_unused_4104_ = lean_ctor_get(v_snd_3986_, 2);
lean_dec(v_unused_4104_);
v_unused_4105_ = lean_ctor_get(v_snd_3986_, 1);
lean_dec(v_unused_4105_);
v_unused_4106_ = lean_ctor_get(v_snd_3986_, 0);
lean_dec(v_unused_4106_);
v___x_4014_ = v_snd_3986_;
v_isShared_4015_ = v_isSharedCheck_4103_;
goto v_resetjp_4013_;
}
else
{
lean_dec(v_snd_3986_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4103_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v_array_4016_; lean_object* v_start_4017_; lean_object* v_stop_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4023_; 
v_array_4016_ = lean_ctor_get(v_fst_3995_, 0);
v_start_4017_ = lean_ctor_get(v_fst_3995_, 1);
v_stop_4018_ = lean_ctor_get(v_fst_3995_, 2);
v___x_4019_ = lean_array_fget(v_array_3999_, v_start_4000_);
v___x_4020_ = lean_unsigned_to_nat(1u);
v___x_4021_ = lean_nat_add(v_start_4000_, v___x_4020_);
lean_dec(v_start_4000_);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 1, v___x_4021_);
v___x_4023_ = v___x_4014_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_array_3999_);
lean_ctor_set(v_reuseFailAlloc_4102_, 1, v___x_4021_);
lean_ctor_set(v_reuseFailAlloc_4102_, 2, v_stop_4001_);
v___x_4023_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
uint8_t v___x_4024_; 
v___x_4024_ = lean_nat_dec_lt(v_start_4017_, v_stop_4018_);
if (v___x_4024_ == 0)
{
lean_object* v___x_4026_; 
lean_dec(v___x_4019_);
lean_dec(v_a_3970_);
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 1, v___x_4023_);
v___x_4026_ = v___x_3997_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_fst_3995_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v___x_4023_);
v___x_4026_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
lean_object* v___x_4028_; 
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 1, v___x_4026_);
v___x_4028_ = v___x_3993_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_fst_3991_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4030_; 
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 1, v___x_4028_);
v___x_4030_ = v___x_3989_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_fst_3987_);
lean_ctor_set(v_reuseFailAlloc_4032_, 1, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4031_; 
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
return v___x_4031_;
}
}
}
}
else
{
lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4098_; 
lean_inc(v_stop_4018_);
lean_inc(v_start_4017_);
lean_inc_ref(v_array_4016_);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_fst_3995_);
if (v_isSharedCheck_4098_ == 0)
{
lean_object* v_unused_4099_; lean_object* v_unused_4100_; lean_object* v_unused_4101_; 
v_unused_4099_ = lean_ctor_get(v_fst_3995_, 2);
lean_dec(v_unused_4099_);
v_unused_4100_ = lean_ctor_get(v_fst_3995_, 1);
lean_dec(v_unused_4100_);
v_unused_4101_ = lean_ctor_get(v_fst_3995_, 0);
lean_dec(v_unused_4101_);
v___x_4036_ = v_fst_3995_;
v_isShared_4037_ = v_isSharedCheck_4098_;
goto v_resetjp_4035_;
}
else
{
lean_dec(v_fst_3995_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4098_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4038_; lean_object* v___x_4040_; 
v___x_4038_ = lean_nat_add(v_start_4017_, v___x_4020_);
lean_dec(v_start_4017_);
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 1, v___x_4038_);
v___x_4040_ = v___x_4036_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_array_4016_);
lean_ctor_set(v_reuseFailAlloc_4097_, 1, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4097_, 2, v_stop_4018_);
v___x_4040_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
if (lean_obj_tag(v___x_4019_) == 1)
{
lean_object* v_val_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4085_; 
v_val_4041_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4043_ = v___x_4019_;
v_isShared_4044_ = v_isSharedCheck_4085_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_val_4041_);
lean_dec(v___x_4019_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4085_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4050_; 
v___x_4045_ = lean_unsigned_to_nat(0u);
v___x_4046_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4047_ = lean_box(0);
v___x_4048_ = lean_array_get(v___x_4047_, v_val_4041_, v___x_4045_);
lean_dec(v_val_4041_);
lean_inc(v_a_3970_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 0, v_a_3970_);
v___x_4050_ = v___x_4043_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_3970_);
v___x_4050_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
uint8_t v___x_4051_; 
v___x_4051_ = l_Option_instDecidableEq___redArg(v___x_4046_, v___x_4048_, v___x_4050_);
if (v___x_4051_ == 0)
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
lean_dec_ref(v___x_4040_);
lean_dec_ref(v___x_4023_);
lean_del_object(v___x_3997_);
lean_del_object(v___x_3993_);
lean_dec(v_fst_3991_);
lean_del_object(v___x_3989_);
lean_dec(v_fst_3987_);
v___x_4052_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4053_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4052_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4063_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4056_ = v___x_4053_;
v_isShared_4057_ = v_isSharedCheck_4063_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4053_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4063_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
if (lean_obj_tag(v_a_4054_) == 0)
{
lean_object* v_a_4058_; lean_object* v___x_4060_; 
lean_dec(v_a_3970_);
v_a_4058_ = lean_ctor_get(v_a_4054_, 0);
lean_inc(v_a_4058_);
lean_dec_ref(v_a_4054_);
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 0, v_a_4058_);
v___x_4060_ = v___x_4056_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4058_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
else
{
lean_object* v_a_4062_; 
lean_del_object(v___x_4056_);
v_a_4062_ = lean_ctor_get(v_a_4054_, 0);
lean_inc(v_a_4062_);
lean_dec_ref(v_a_4054_);
v_a_3978_ = v_a_4062_;
goto v___jp_3977_;
}
}
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec(v_a_3970_);
v_a_4064_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4053_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4053_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
else
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4076_; 
lean_inc(v_fst_3991_);
v___x_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4072_, 0, v_fst_3991_);
v___x_4073_ = lean_array_push(v_fst_3987_, v___x_4072_);
v___x_4074_ = lean_nat_add(v_fst_3991_, v___x_4020_);
lean_dec(v_fst_3991_);
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 1, v___x_4023_);
lean_ctor_set(v___x_3997_, 0, v___x_4040_);
v___x_4076_ = v___x_3997_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v___x_4040_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v___x_4023_);
v___x_4076_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4078_; 
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 1, v___x_4076_);
lean_ctor_set(v___x_3993_, 0, v___x_4074_);
v___x_4078_ = v___x_3993_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4074_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v___x_4076_);
v___x_4078_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
lean_object* v___x_4080_; 
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 1, v___x_4078_);
lean_ctor_set(v___x_3989_, 0, v___x_4073_);
v___x_4080_ = v___x_3989_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4073_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v___x_4078_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
v_a_3978_ = v___x_4080_;
goto v___jp_3977_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4089_; 
lean_dec(v___x_4019_);
v___x_4086_ = lean_box(0);
v___x_4087_ = lean_array_push(v_fst_3987_, v___x_4086_);
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 1, v___x_4023_);
lean_ctor_set(v___x_3997_, 0, v___x_4040_);
v___x_4089_ = v___x_3997_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4040_);
lean_ctor_set(v_reuseFailAlloc_4096_, 1, v___x_4023_);
v___x_4089_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
lean_object* v___x_4091_; 
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 1, v___x_4089_);
v___x_4091_ = v___x_3993_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_fst_3991_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v___x_4089_);
v___x_4091_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
lean_object* v___x_4093_; 
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 1, v___x_4091_);
lean_ctor_set(v___x_3989_, 0, v___x_4087_);
v___x_4093_ = v___x_3989_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4087_);
lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4091_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
v_a_3978_ = v___x_4093_;
goto v___jp_3977_;
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
v___jp_3977_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3979_ = lean_unsigned_to_nat(1u);
v___x_3980_ = lean_nat_add(v_a_3970_, v___x_3979_);
lean_dec(v_a_3970_);
v_a_3970_ = v___x_3980_;
v_b_3971_ = v_a_3978_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4113_, lean_object* v_a_4114_, lean_object* v_b_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4113_, v_a_4114_, v_b_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v_upperBound_4113_);
return v_res_4121_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4123_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4124_ = lean_unsigned_to_nat(4u);
v___x_4125_ = lean_unsigned_to_nat(275u);
v___x_4126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4127_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4128_ = l_mkPanicMessageWithDecl(v___x_4127_, v___x_4126_, v___x_4125_, v___x_4124_, v___x_4123_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4129_, lean_object* v___x_4130_, lean_object* v___x_4131_, lean_object* v_xs_4132_, lean_object* v_x_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v_graph_4139_; lean_object* v_revDeps_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4193_; 
v_graph_4139_ = lean_ctor_get(v_a_4129_, 0);
v_revDeps_4140_ = lean_ctor_get(v_a_4129_, 1);
v_isSharedCheck_4193_ = !lean_is_exclusive(v_a_4129_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4142_ = v_a_4129_;
v_isShared_4143_ = v_isSharedCheck_4193_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_revDeps_4140_);
lean_inc(v_graph_4139_);
lean_dec(v_a_4129_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4193_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; uint8_t v___x_4147_; 
v___x_4144_ = lean_array_get_borrowed(v___x_4130_, v_graph_4139_, v___x_4131_);
v___x_4145_ = lean_array_get_size(v_xs_4132_);
v___x_4146_ = lean_array_get_size(v___x_4144_);
v___x_4147_ = lean_nat_dec_eq(v___x_4145_, v___x_4146_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
lean_del_object(v___x_4142_);
lean_dec_ref(v_revDeps_4140_);
lean_dec_ref(v_graph_4139_);
lean_dec_ref(v_xs_4132_);
lean_dec(v___x_4131_);
v___x_4148_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4149_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4148_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
return v___x_4149_;
}
else
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4154_; 
v___x_4150_ = lean_mk_empty_array_with_capacity(v___x_4131_);
lean_inc_n(v___x_4131_, 2);
v___x_4151_ = l_Array_toSubarray___redArg(v_xs_4132_, v___x_4131_, v___x_4145_);
lean_inc(v___x_4144_);
v___x_4152_ = l_Array_toSubarray___redArg(v___x_4144_, v___x_4131_, v___x_4146_);
if (v_isShared_4143_ == 0)
{
lean_ctor_set(v___x_4142_, 1, v___x_4152_);
lean_ctor_set(v___x_4142_, 0, v___x_4151_);
v___x_4154_ = v___x_4142_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_4151_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v___x_4152_);
v___x_4154_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
lean_inc(v___x_4131_);
v___x_4155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4131_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
v___x_4156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4150_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4145_, v___x_4131_, v___x_4156_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v_snd_4159_; lean_object* v_fst_4160_; lean_object* v_fst_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref(v___x_4157_);
v_snd_4159_ = lean_ctor_get(v_a_4158_, 1);
lean_inc(v_snd_4159_);
v_fst_4160_ = lean_ctor_get(v_a_4158_, 0);
lean_inc_n(v_fst_4160_, 2);
lean_dec(v_a_4158_);
v_fst_4161_ = lean_ctor_get(v_snd_4159_, 0);
lean_inc(v_fst_4161_);
lean_dec(v_snd_4159_);
v___x_4162_ = lean_unsigned_to_nat(1u);
v___x_4163_ = lean_array_get_size(v_graph_4139_);
v___x_4164_ = lean_mk_empty_array_with_capacity(v___x_4162_);
v___x_4165_ = lean_array_push(v___x_4164_, v_fst_4160_);
v___x_4166_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4163_, v_graph_4139_, v_fst_4160_, v___x_4162_, v___x_4165_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
lean_dec(v_fst_4160_);
lean_dec_ref(v_graph_4139_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4175_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4169_ = v___x_4166_;
v_isShared_4170_ = v_isSharedCheck_4175_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4166_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4175_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4171_; lean_object* v___x_4173_; 
v___x_4171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4171_, 0, v_fst_4161_);
lean_ctor_set(v___x_4171_, 1, v_a_4167_);
lean_ctor_set(v___x_4171_, 2, v_revDeps_4140_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 0, v___x_4171_);
v___x_4173_ = v___x_4169_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_dec(v_fst_4161_);
lean_dec_ref(v_revDeps_4140_);
v_a_4176_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4166_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4166_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
lean_dec_ref(v_revDeps_4140_);
lean_dec_ref(v_graph_4139_);
v_a_4184_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4157_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4157_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4194_, lean_object* v___x_4195_, lean_object* v___x_4196_, lean_object* v_xs_4197_, lean_object* v_x_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4194_, v___x_4195_, v___x_4196_, v_xs_4197_, v_x_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec_ref(v_x_4198_);
lean_dec_ref(v___x_4195_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_){
_start:
{
lean_object* v___x_4211_; 
lean_inc_ref(v_preDefs_4205_);
v___x_4211_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v_a_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v_value_4216_; lean_object* v___x_4217_; lean_object* v___f_4218_; uint8_t v___x_4219_; lean_object* v___x_4220_; 
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
lean_inc(v_a_4212_);
lean_dec_ref(v___x_4211_);
v___x_4213_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4214_ = lean_unsigned_to_nat(0u);
v___x_4215_ = lean_array_get(v___x_4213_, v_preDefs_4205_, v___x_4214_);
lean_dec_ref(v_preDefs_4205_);
v_value_4216_ = lean_ctor_get(v___x_4215_, 7);
lean_inc_ref(v_value_4216_);
lean_dec(v___x_4215_);
v___x_4217_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4218_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4218_, 0, v_a_4212_);
lean_closure_set(v___f_4218_, 1, v___x_4217_);
lean_closure_set(v___f_4218_, 2, v___x_4214_);
v___x_4219_ = 0;
v___x_4220_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4216_, v___f_4218_, v___x_4219_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_);
return v___x_4220_;
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_dec_ref(v_preDefs_4205_);
v_a_4221_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4211_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4211_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_);
lean_dec(v_a_4233_);
lean_dec_ref(v_a_4232_);
lean_dec(v_a_4231_);
lean_dec_ref(v_a_4230_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4236_, lean_object* v___x_4237_, lean_object* v___x_4238_, lean_object* v_inst_4239_, lean_object* v_R_4240_, lean_object* v_a_4241_, lean_object* v_b_4242_, lean_object* v_c_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v___x_4249_; 
v___x_4249_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4236_, v___x_4237_, v___x_4238_, v_a_4241_, v_b_4242_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4250_, lean_object* v___x_4251_, lean_object* v___x_4252_, lean_object* v_inst_4253_, lean_object* v_R_4254_, lean_object* v_a_4255_, lean_object* v_b_4256_, lean_object* v_c_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4250_, v___x_4251_, v___x_4252_, v_inst_4253_, v_R_4254_, v_a_4255_, v_b_4256_, v_c_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec_ref(v___x_4252_);
lean_dec_ref(v___x_4251_);
lean_dec(v_upperBound_4250_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4264_, lean_object* v_inst_4265_, lean_object* v_R_4266_, lean_object* v_a_4267_, lean_object* v_b_4268_, lean_object* v_c_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4264_, v_a_4267_, v_b_4268_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4276_, lean_object* v_inst_4277_, lean_object* v_R_4278_, lean_object* v_a_4279_, lean_object* v_b_4280_, lean_object* v_c_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4276_, v_inst_4277_, v_R_4278_, v_a_4279_, v_b_4280_, v_c_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v_upperBound_4276_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4288_, size_t v_i_4289_, size_t v_stop_4290_, lean_object* v_b_4291_){
_start:
{
uint8_t v___x_4292_; 
v___x_4292_ = lean_usize_dec_eq(v_i_4289_, v_stop_4290_);
if (v___x_4292_ == 0)
{
size_t v___x_4293_; size_t v___x_4294_; lean_object* v___x_4295_; 
v___x_4293_ = ((size_t)1ULL);
v___x_4294_ = lean_usize_sub(v_i_4289_, v___x_4293_);
v___x_4295_ = lean_array_uget_borrowed(v_as_4288_, v___x_4294_);
if (lean_obj_tag(v___x_4295_) == 0)
{
v_i_4289_ = v___x_4294_;
goto _start;
}
else
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4297_ = lean_unsigned_to_nat(1u);
v___x_4298_ = lean_nat_add(v_b_4291_, v___x_4297_);
lean_dec(v_b_4291_);
v_i_4289_ = v___x_4294_;
v_b_4291_ = v___x_4298_;
goto _start;
}
}
else
{
return v_b_4291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4300_, lean_object* v_i_4301_, lean_object* v_stop_4302_, lean_object* v_b_4303_){
_start:
{
size_t v_i_boxed_4304_; size_t v_stop_boxed_4305_; lean_object* v_res_4306_; 
v_i_boxed_4304_ = lean_unbox_usize(v_i_4301_);
lean_dec(v_i_4301_);
v_stop_boxed_4305_ = lean_unbox_usize(v_stop_4302_);
lean_dec(v_stop_4302_);
v_res_4306_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4300_, v_i_boxed_4304_, v_stop_boxed_4305_, v_b_4303_);
lean_dec_ref(v_as_4300_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4307_){
_start:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; 
v___x_4308_ = lean_unsigned_to_nat(0u);
v___x_4309_ = lean_array_get_size(v_perm_4307_);
v___x_4310_ = lean_nat_dec_lt(v___x_4308_, v___x_4309_);
if (v___x_4310_ == 0)
{
return v___x_4308_;
}
else
{
size_t v___x_4311_; size_t v___x_4312_; lean_object* v___x_4313_; 
v___x_4311_ = lean_usize_of_nat(v___x_4309_);
v___x_4312_ = ((size_t)0ULL);
v___x_4313_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4307_, v___x_4311_, v___x_4312_, v___x_4308_);
return v___x_4313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4314_);
lean_dec_ref(v_perm_4314_);
return v_res_4315_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4316_, lean_object* v_i_4317_){
_start:
{
lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4318_ = lean_array_get_size(v_perm_4316_);
v___x_4319_ = lean_nat_dec_lt(v_i_4317_, v___x_4318_);
if (v___x_4319_ == 0)
{
return v___x_4319_;
}
else
{
lean_object* v___x_4320_; 
v___x_4320_ = lean_array_fget_borrowed(v_perm_4316_, v_i_4317_);
if (lean_obj_tag(v___x_4320_) == 0)
{
uint8_t v___x_4321_; 
v___x_4321_ = 0;
return v___x_4321_;
}
else
{
return v___x_4319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4322_, lean_object* v_i_4323_){
_start:
{
uint8_t v_res_4324_; lean_object* v_r_4325_; 
v_res_4324_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4322_, v_i_4323_);
lean_dec(v_i_4323_);
lean_dec_ref(v_perm_4322_);
v_r_4325_ = lean_box(v_res_4324_);
return v_r_4325_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v___f_4332_; lean_object* v___x_1076__overap_4333_; lean_object* v___x_4334_; 
v___f_4332_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_1076__overap_4333_ = lean_panic_fn_borrowed(v___f_4332_, v_msg_4326_);
lean_inc(v___y_4330_);
lean_inc_ref(v___y_4329_);
lean_inc(v___y_4328_);
lean_inc_ref(v___y_4327_);
v___x_4334_ = lean_apply_5(v___x_1076__overap_4333_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, lean_box(0));
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4342_, lean_object* v_msg_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
lean_object* v___x_4349_; 
v___x_4349_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
return v___x_4349_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4350_, lean_object* v_msg_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4350_, v_msg_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4358_, lean_object* v_maxFVars_x3f_4359_, lean_object* v_k_4360_, uint8_t v_cleanupAnnotations_4361_, uint8_t v_whnfType_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_){
_start:
{
lean_object* v___f_4368_; lean_object* v___x_4369_; 
v___f_4368_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4368_, 0, v_k_4360_);
v___x_4369_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4358_, v_maxFVars_x3f_4359_, v___f_4368_, v_cleanupAnnotations_4361_, v_whnfType_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4377_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4372_ = v___x_4369_;
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4369_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4375_; 
if (v_isShared_4373_ == 0)
{
v___x_4375_ = v___x_4372_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_a_4370_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
else
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4385_; 
v_a_4378_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4380_ = v___x_4369_;
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4369_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4378_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4386_, lean_object* v_maxFVars_x3f_4387_, lean_object* v_k_4388_, lean_object* v_cleanupAnnotations_4389_, lean_object* v_whnfType_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4396_; uint8_t v_whnfType_boxed_4397_; lean_object* v_res_4398_; 
v_cleanupAnnotations_boxed_4396_ = lean_unbox(v_cleanupAnnotations_4389_);
v_whnfType_boxed_4397_ = lean_unbox(v_whnfType_4390_);
v_res_4398_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4386_, v_maxFVars_x3f_4387_, v_k_4388_, v_cleanupAnnotations_boxed_4396_, v_whnfType_boxed_4397_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4399_, lean_object* v_type_4400_, lean_object* v_maxFVars_x3f_4401_, lean_object* v_k_4402_, uint8_t v_cleanupAnnotations_4403_, uint8_t v_whnfType_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v___x_4410_; 
v___x_4410_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4400_, v_maxFVars_x3f_4401_, v_k_4402_, v_cleanupAnnotations_4403_, v_whnfType_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4411_, lean_object* v_type_4412_, lean_object* v_maxFVars_x3f_4413_, lean_object* v_k_4414_, lean_object* v_cleanupAnnotations_4415_, lean_object* v_whnfType_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4422_; uint8_t v_whnfType_boxed_4423_; lean_object* v_res_4424_; 
v_cleanupAnnotations_boxed_4422_ = lean_unbox(v_cleanupAnnotations_4415_);
v_whnfType_boxed_4423_ = lean_unbox(v_whnfType_4416_);
v_res_4424_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4411_, v_type_4412_, v_maxFVars_x3f_4413_, v_k_4414_, v_cleanupAnnotations_boxed_4422_, v_whnfType_boxed_4423_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
return v_res_4424_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4427_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4428_ = lean_unsigned_to_nat(6u);
v___x_4429_ = lean_unsigned_to_nat(329u);
v___x_4430_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4431_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4432_ = l_mkPanicMessageWithDecl(v___x_4431_, v___x_4430_, v___x_4429_, v___x_4428_, v___x_4427_);
return v___x_4432_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4436_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4437_ = lean_unsigned_to_nat(8u);
v___x_4438_ = lean_unsigned_to_nat(322u);
v___x_4439_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4440_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4441_ = l_mkPanicMessageWithDecl(v___x_4440_, v___x_4439_, v___x_4438_, v___x_4437_, v___x_4436_);
return v___x_4441_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4443_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4444_ = lean_unsigned_to_nat(8u);
v___x_4445_ = lean_unsigned_to_nat(325u);
v___x_4446_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4447_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4448_ = l_mkPanicMessageWithDecl(v___x_4447_, v___x_4446_, v___x_4445_, v___x_4444_, v___x_4443_);
return v___x_4448_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4450_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4451_ = lean_unsigned_to_nat(8u);
v___x_4452_ = lean_unsigned_to_nat(324u);
v___x_4453_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4454_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4455_ = l_mkPanicMessageWithDecl(v___x_4454_, v___x_4453_, v___x_4452_, v___x_4451_, v___x_4450_);
return v___x_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4456_, lean_object* v_xs_4457_, lean_object* v_val_4458_, lean_object* v_i_4459_, lean_object* v_perm_4460_, lean_object* v_k_4461_, lean_object* v_xs_x27_4462_, lean_object* v_type_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v___x_4469_; uint8_t v___x_4470_; 
v___x_4469_ = lean_array_get_size(v_xs_x27_4462_);
v___x_4470_ = lean_nat_dec_eq(v___x_4469_, v___x_4456_);
if (v___x_4470_ == 0)
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
lean_dec_ref(v_type_4463_);
lean_dec_ref(v_k_4461_);
lean_dec_ref(v_perm_4460_);
lean_dec_ref(v_xs_4457_);
v___x_4471_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4472_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4471_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
return v___x_4472_;
}
else
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v_x_4475_; lean_object* v___x_4476_; 
v___x_4473_ = l_Lean_instInhabitedExpr;
v___x_4474_ = lean_unsigned_to_nat(0u);
v_x_4475_ = lean_array_get_borrowed(v___x_4473_, v_xs_x27_4462_, v___x_4474_);
lean_inc(v___y_4467_);
lean_inc_ref(v___y_4466_);
lean_inc(v___y_4465_);
lean_inc_ref(v___y_4464_);
lean_inc(v_x_4475_);
v___x_4476_ = lean_infer_type(v_x_4475_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; uint8_t v___x_4478_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref(v___x_4476_);
v___x_4478_ = l_Lean_Expr_hasLooseBVars(v_a_4477_);
lean_dec(v_a_4477_);
if (v___x_4478_ == 0)
{
lean_object* v___x_4479_; uint8_t v___x_4480_; 
v___x_4479_ = lean_array_get_size(v_xs_4457_);
v___x_4480_ = lean_nat_dec_lt(v_val_4458_, v___x_4479_);
if (v___x_4480_ == 0)
{
lean_object* v___x_4481_; lean_object* v___x_4482_; 
lean_dec_ref(v_type_4463_);
lean_dec_ref(v_k_4461_);
lean_dec_ref(v_perm_4460_);
lean_dec_ref(v_xs_4457_);
v___x_4481_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4482_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4481_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
return v___x_4482_;
}
else
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4483_ = lean_nat_add(v_i_4459_, v___x_4456_);
lean_inc(v_x_4475_);
v___x_4484_ = lean_array_set(v_xs_4457_, v_val_4458_, v_x_4475_);
v___x_4485_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4460_, v_k_4461_, v___x_4483_, v_type_4463_, v___x_4484_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
return v___x_4485_;
}
}
else
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
lean_dec_ref(v_type_4463_);
lean_dec_ref(v_k_4461_);
lean_dec_ref(v_perm_4460_);
lean_dec_ref(v_xs_4457_);
v___x_4486_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4487_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4486_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
return v___x_4487_;
}
}
else
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
lean_dec_ref(v_type_4463_);
lean_dec_ref(v_k_4461_);
lean_dec_ref(v_perm_4460_);
lean_dec_ref(v_xs_4457_);
v_a_4488_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4490_ = v___x_4476_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4476_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4496_, lean_object* v_xs_4497_, lean_object* v_val_4498_, lean_object* v_i_4499_, lean_object* v_perm_4500_, lean_object* v_k_4501_, lean_object* v_xs_x27_4502_, lean_object* v_type_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
lean_object* v_res_4509_; 
v_res_4509_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4496_, v_xs_4497_, v_val_4498_, v_i_4499_, v_perm_4500_, v_k_4501_, v_xs_x27_4502_, v_type_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec_ref(v_xs_x27_4502_);
lean_dec(v_i_4499_);
lean_dec(v_val_4498_);
lean_dec(v___x_4496_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4510_, lean_object* v_k_4511_, lean_object* v_i_4512_, lean_object* v_type_4513_, lean_object* v_xs_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_){
_start:
{
lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4520_ = lean_array_get_size(v_perm_4510_);
v___x_4521_ = lean_nat_dec_lt(v_i_4512_, v___x_4520_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; 
lean_dec_ref(v_type_4513_);
lean_dec(v_i_4512_);
lean_dec_ref(v_perm_4510_);
lean_inc(v_a_4518_);
lean_inc_ref(v_a_4517_);
lean_inc(v_a_4516_);
lean_inc_ref(v_a_4515_);
v___x_4522_ = lean_apply_6(v_k_4511_, v_xs_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, lean_box(0));
return v___x_4522_;
}
else
{
lean_object* v___x_4523_; 
v___x_4523_ = lean_array_fget_borrowed(v_perm_4510_, v_i_4512_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_object* v___x_4524_; 
lean_inc(v_a_4518_);
lean_inc_ref(v_a_4517_);
lean_inc(v_a_4516_);
lean_inc_ref(v_a_4515_);
v___x_4524_ = lean_whnf(v_type_4513_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; uint8_t v___x_4526_; 
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_a_4525_);
lean_dec_ref(v___x_4524_);
v___x_4526_ = l_Lean_Expr_isForall(v_a_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; lean_object* v___x_4528_; 
lean_dec(v_a_4525_);
lean_dec_ref(v_xs_4514_);
lean_dec(v_i_4512_);
lean_dec_ref(v_k_4511_);
lean_dec_ref(v_perm_4510_);
v___x_4527_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4528_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4527_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_);
return v___x_4528_;
}
else
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4529_ = lean_unsigned_to_nat(1u);
v___x_4530_ = lean_nat_add(v_i_4512_, v___x_4529_);
lean_dec(v_i_4512_);
v___x_4531_ = l_Lean_Expr_bindingBody_x21(v_a_4525_);
lean_dec(v_a_4525_);
v_i_4512_ = v___x_4530_;
v_type_4513_ = v___x_4531_;
goto _start;
}
}
else
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
lean_dec_ref(v_xs_4514_);
lean_dec(v_i_4512_);
lean_dec_ref(v_k_4511_);
lean_dec_ref(v_perm_4510_);
v_a_4533_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___x_4524_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4524_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4533_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
}
else
{
lean_object* v_val_4541_; lean_object* v___x_4542_; lean_object* v___f_4543_; lean_object* v___x_4544_; uint8_t v___x_4545_; lean_object* v___x_4546_; 
v_val_4541_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_val_4541_);
v___x_4542_ = lean_unsigned_to_nat(1u);
v___f_4543_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4543_, 0, v___x_4542_);
lean_closure_set(v___f_4543_, 1, v_xs_4514_);
lean_closure_set(v___f_4543_, 2, v_val_4541_);
lean_closure_set(v___f_4543_, 3, v_i_4512_);
lean_closure_set(v___f_4543_, 4, v_perm_4510_);
lean_closure_set(v___f_4543_, 5, v_k_4511_);
v___x_4544_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4545_ = 0;
v___x_4546_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4513_, v___x_4544_, v___f_4543_, v___x_4521_, v___x_4545_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_);
return v___x_4546_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4547_, lean_object* v_k_4548_, lean_object* v_i_4549_, lean_object* v_type_4550_, lean_object* v_xs_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4547_, v_k_4548_, v_i_4549_, v_type_4550_, v_xs_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_);
lean_dec(v_a_4555_);
lean_dec_ref(v_a_4554_);
lean_dec(v_a_4553_);
lean_dec_ref(v_a_4552_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4558_, lean_object* v_perm_4559_, lean_object* v_k_4560_, lean_object* v_i_4561_, lean_object* v_type_4562_, lean_object* v_xs_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v___x_4569_; 
v___x_4569_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4559_, v_k_4560_, v_i_4561_, v_type_4562_, v_xs_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4570_, lean_object* v_perm_4571_, lean_object* v_k_4572_, lean_object* v_i_4573_, lean_object* v_type_4574_, lean_object* v_xs_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4570_, v_perm_4571_, v_k_4572_, v_i_4573_, v_type_4574_, v_xs_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_);
lean_dec(v_a_4579_);
lean_dec_ref(v_a_4578_);
lean_dec(v_a_4577_);
lean_dec_ref(v_a_4576_);
return v_res_4581_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4582_ = lean_unsigned_to_nat(0u);
v___x_4583_ = l_Lean_Level_ofNat(v___x_4582_);
return v___x_4583_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4584_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4585_ = l_Lean_mkSort(v___x_4584_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4586_, lean_object* v_type_4587_, lean_object* v_k_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4594_ = lean_unsigned_to_nat(0u);
v___x_4595_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4586_);
v___x_4596_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4597_ = lean_mk_array(v___x_4595_, v___x_4596_);
v___x_4598_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4586_, v_k_4588_, v___x_4594_, v_type_4587_, v___x_4597_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
return v___x_4598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4599_, lean_object* v_type_4600_, lean_object* v_k_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4599_, v_type_4600_, v_k_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_);
lean_dec(v_a_4605_);
lean_dec_ref(v_a_4604_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4608_, lean_object* v_perm_4609_, lean_object* v_type_4610_, lean_object* v_k_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4609_, v_type_4610_, v_k_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4618_, lean_object* v_perm_4619_, lean_object* v_type_4620_, lean_object* v_k_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4618_, v_perm_4619_, v_type_4620_, v_k_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4628_, lean_object* v_runInBase_4629_, lean_object* v_b_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = lean_apply_1(v_k_4628_, v_b_4630_);
lean_inc(v___y_4634_);
lean_inc_ref(v___y_4633_);
lean_inc(v___y_4632_);
lean_inc_ref(v___y_4631_);
v___x_4637_ = lean_apply_7(v_runInBase_4629_, lean_box(0), v___x_4636_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, lean_box(0));
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4638_, lean_object* v_runInBase_4639_, lean_object* v_b_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4638_, v_runInBase_4639_, v_b_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
lean_dec(v___y_4644_);
lean_dec_ref(v___y_4643_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4647_, lean_object* v_perm_4648_, lean_object* v_type_4649_, lean_object* v_runInBase_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v___f_4656_; lean_object* v___x_4657_; 
v___f_4656_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4656_, 0, v_k_4647_);
lean_closure_set(v___f_4656_, 1, v_runInBase_4650_);
v___x_4657_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4648_, v_type_4649_, v___f_4656_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4658_, lean_object* v_perm_4659_, lean_object* v_type_4660_, lean_object* v_runInBase_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4658_, v_perm_4659_, v_type_4660_, v_runInBase_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4668_, lean_object* v_inst_4669_, lean_object* v_perm_4670_, lean_object* v_type_4671_, lean_object* v_k_4672_){
_start:
{
lean_object* v_toBind_4673_; lean_object* v_liftWith_4674_; lean_object* v_restoreM_4675_; lean_object* v___f_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v_toBind_4673_ = lean_ctor_get(v_inst_4669_, 1);
lean_inc(v_toBind_4673_);
lean_dec_ref(v_inst_4669_);
v_liftWith_4674_ = lean_ctor_get(v_inst_4668_, 0);
lean_inc(v_liftWith_4674_);
v_restoreM_4675_ = lean_ctor_get(v_inst_4668_, 1);
lean_inc(v_restoreM_4675_);
lean_dec_ref(v_inst_4668_);
v___f_4676_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4676_, 0, v_k_4672_);
lean_closure_set(v___f_4676_, 1, v_perm_4670_);
lean_closure_set(v___f_4676_, 2, v_type_4671_);
v___x_4677_ = lean_apply_2(v_liftWith_4674_, lean_box(0), v___f_4676_);
v___x_4678_ = lean_apply_1(v_restoreM_4675_, lean_box(0));
v___x_4679_ = lean_apply_4(v_toBind_4673_, lean_box(0), lean_box(0), v___x_4677_, v___x_4678_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4680_, lean_object* v_00_u03b1_4681_, lean_object* v_inst_4682_, lean_object* v_inst_4683_, lean_object* v_perm_4684_, lean_object* v_type_4685_, lean_object* v_k_4686_){
_start:
{
lean_object* v___x_4687_; 
v___x_4687_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4682_, v_inst_4683_, v_perm_4684_, v_type_4685_, v_k_4686_);
return v___x_4687_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_){
_start:
{
lean_object* v___f_4694_; lean_object* v___x_603__overap_4695_; lean_object* v___x_4696_; 
v___f_4694_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_603__overap_4695_ = lean_panic_fn_borrowed(v___f_4694_, v_msg_4688_);
lean_inc(v___y_4692_);
lean_inc_ref(v___y_4691_);
lean_inc(v___y_4690_);
lean_inc_ref(v___y_4689_);
v___x_4696_ = lean_apply_5(v___x_603__overap_4695_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, lean_box(0));
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_){
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
return v_res_4703_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4706_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4707_ = lean_unsigned_to_nat(10u);
v___x_4708_ = lean_unsigned_to_nat(353u);
v___x_4709_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4710_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4711_ = l_mkPanicMessageWithDecl(v___x_4710_, v___x_4709_, v___x_4708_, v___x_4707_, v___x_4706_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4712_, lean_object* v_xs_4713_, lean_object* v_tail_4714_, lean_object* v_ys_4715_, lean_object* v_type_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v_res_4722_; 
v_res_4722_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4712_, v_xs_4713_, v_tail_4714_, v_ys_4715_, v_type_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec_ref(v_ys_4715_);
lean_dec(v___x_4712_);
return v_res_4722_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4723_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4724_ = lean_unsigned_to_nat(8u);
v___x_4725_ = lean_unsigned_to_nat(349u);
v___x_4726_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4727_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4728_ = l_mkPanicMessageWithDecl(v___x_4727_, v___x_4726_, v___x_4725_, v___x_4724_, v___x_4723_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4729_, lean_object* v_x_4730_, lean_object* v_x_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
if (lean_obj_tag(v_x_4730_) == 0)
{
lean_object* v___x_4737_; 
lean_dec_ref(v_xs_4729_);
v___x_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4737_, 0, v_x_4731_);
return v___x_4737_;
}
else
{
lean_object* v_head_4738_; 
v_head_4738_ = lean_ctor_get(v_x_4730_, 0);
if (lean_obj_tag(v_head_4738_) == 0)
{
lean_object* v_tail_4739_; lean_object* v___x_4740_; lean_object* v___f_4741_; lean_object* v___x_4742_; uint8_t v___x_4743_; lean_object* v___x_4744_; 
v_tail_4739_ = lean_ctor_get(v_x_4730_, 1);
lean_inc(v_tail_4739_);
lean_dec_ref(v_x_4730_);
v___x_4740_ = lean_unsigned_to_nat(1u);
v___f_4741_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4741_, 0, v___x_4740_);
lean_closure_set(v___f_4741_, 1, v_xs_4729_);
lean_closure_set(v___f_4741_, 2, v_tail_4739_);
v___x_4742_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4743_ = 0;
v___x_4744_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4731_, v___x_4742_, v___f_4741_, v___x_4743_, v___x_4743_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_);
return v___x_4744_;
}
else
{
lean_object* v_tail_4745_; lean_object* v_val_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; 
lean_inc_ref(v_head_4738_);
v_tail_4745_ = lean_ctor_get(v_x_4730_, 1);
lean_inc(v_tail_4745_);
lean_dec_ref(v_x_4730_);
v_val_4746_ = lean_ctor_get(v_head_4738_, 0);
lean_inc(v_val_4746_);
lean_dec_ref(v_head_4738_);
v___x_4747_ = lean_array_get_size(v_xs_4729_);
v___x_4748_ = lean_nat_dec_lt(v_val_4746_, v___x_4747_);
if (v___x_4748_ == 0)
{
lean_object* v___x_4749_; lean_object* v___x_4750_; 
lean_dec(v_val_4746_);
lean_dec(v_tail_4745_);
lean_dec_ref(v_x_4731_);
lean_dec_ref(v_xs_4729_);
v___x_4749_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4750_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4749_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_);
return v___x_4750_;
}
else
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4751_ = l_Lean_instInhabitedExpr;
v___x_4752_ = lean_array_get_borrowed(v___x_4751_, v_xs_4729_, v_val_4746_);
lean_dec(v_val_4746_);
v___x_4753_ = lean_unsigned_to_nat(1u);
v___x_4754_ = lean_mk_empty_array_with_capacity(v___x_4753_);
lean_inc(v___x_4752_);
v___x_4755_ = lean_array_push(v___x_4754_, v___x_4752_);
v___x_4756_ = l_Lean_Meta_instantiateForall(v_x_4731_, v___x_4755_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_);
lean_dec_ref(v___x_4755_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; 
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
lean_inc(v_a_4757_);
lean_dec_ref(v___x_4756_);
v_x_4730_ = v_tail_4745_;
v_x_4731_ = v_a_4757_;
goto _start;
}
else
{
lean_dec(v_tail_4745_);
lean_dec_ref(v_xs_4729_);
return v___x_4756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4759_, lean_object* v_xs_4760_, lean_object* v_tail_4761_, lean_object* v_ys_4762_, lean_object* v_type_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
lean_object* v___x_4769_; uint8_t v___x_4770_; 
v___x_4769_ = lean_array_get_size(v_ys_4762_);
v___x_4770_ = lean_nat_dec_eq(v___x_4769_, v___x_4759_);
if (v___x_4770_ == 0)
{
lean_object* v___x_4771_; lean_object* v___x_4772_; 
lean_dec_ref(v_type_4763_);
lean_dec(v_tail_4761_);
lean_dec_ref(v_xs_4760_);
v___x_4771_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4772_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4771_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
return v___x_4772_;
}
else
{
lean_object* v___x_4773_; 
v___x_4773_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4760_, v_tail_4761_, v_type_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v_a_4774_; uint8_t v___x_4775_; uint8_t v___x_4776_; lean_object* v___x_4777_; 
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_a_4774_);
lean_dec_ref(v___x_4773_);
v___x_4775_ = 0;
v___x_4776_ = 1;
v___x_4777_ = l_Lean_Meta_mkForallFVars(v_ys_4762_, v_a_4774_, v___x_4775_, v___x_4770_, v___x_4770_, v___x_4776_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
return v___x_4777_;
}
else
{
return v___x_4773_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4778_, lean_object* v_x_4779_, lean_object* v_x_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4778_, v_x_4779_, v_x_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_);
lean_dec(v_a_4784_);
lean_dec_ref(v_a_4783_);
lean_dec(v_a_4782_);
lean_dec_ref(v_a_4781_);
return v_res_4786_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4789_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4790_ = lean_unsigned_to_nat(2u);
v___x_4791_ = lean_unsigned_to_nat(343u);
v___x_4792_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4793_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4794_ = l_mkPanicMessageWithDecl(v___x_4793_, v___x_4792_, v___x_4791_, v___x_4790_, v___x_4789_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4795_, lean_object* v_type_u2080_4796_, lean_object* v_xs_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; uint8_t v___x_4805_; 
v___x_4803_ = lean_array_get_size(v_xs_4797_);
v___x_4804_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4795_);
v___x_4805_ = lean_nat_dec_eq(v___x_4803_, v___x_4804_);
lean_dec(v___x_4804_);
if (v___x_4805_ == 0)
{
lean_object* v___x_4806_; lean_object* v___x_4807_; 
lean_dec_ref(v_xs_4797_);
lean_dec_ref(v_type_u2080_4796_);
lean_dec_ref(v_perm_4795_);
v___x_4806_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4807_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4806_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
return v___x_4807_;
}
else
{
lean_object* v_mask_4808_; lean_object* v___x_4809_; 
v_mask_4808_ = lean_array_to_list(v_perm_4795_);
v___x_4809_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4797_, v_mask_4808_, v_type_u2080_4796_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
return v___x_4809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4810_, lean_object* v_type_u2080_4811_, lean_object* v_xs_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_){
_start:
{
lean_object* v_res_4818_; 
v_res_4818_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4810_, v_type_u2080_4811_, v_xs_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
lean_dec(v_a_4816_);
lean_dec_ref(v_a_4815_);
lean_dec(v_a_4814_);
lean_dec_ref(v_a_4813_);
return v_res_4818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(lean_object* v_e_4819_, lean_object* v_maxFVars_4820_, lean_object* v_k_4821_, uint8_t v_cleanupAnnotations_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_){
_start:
{
lean_object* v___f_4828_; uint8_t v___x_4829_; uint8_t v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___f_4828_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4828_, 0, v_k_4821_);
v___x_4829_ = 1;
v___x_4830_ = 0;
v___x_4831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4831_, 0, v_maxFVars_4820_);
v___x_4832_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4819_, v___x_4829_, v___x_4830_, v___x_4829_, v___x_4830_, v___x_4831_, v___f_4828_, v_cleanupAnnotations_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
lean_dec_ref(v___x_4831_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
v_a_4833_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4832_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4832_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
else
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4848_; 
v_a_4841_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4843_ = v___x_4832_;
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4832_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4846_; 
if (v_isShared_4844_ == 0)
{
v___x_4846_ = v___x_4843_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg___boxed(lean_object* v_e_4849_, lean_object* v_maxFVars_4850_, lean_object* v_k_4851_, lean_object* v_cleanupAnnotations_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4858_; lean_object* v_res_4859_; 
v_cleanupAnnotations_boxed_4858_ = lean_unbox(v_cleanupAnnotations_4852_);
v_res_4859_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(v_e_4849_, v_maxFVars_4850_, v_k_4851_, v_cleanupAnnotations_boxed_4858_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_00_u03b1_4860_, lean_object* v_e_4861_, lean_object* v_maxFVars_4862_, lean_object* v_k_4863_, uint8_t v_cleanupAnnotations_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(v_e_4861_, v_maxFVars_4862_, v_k_4863_, v_cleanupAnnotations_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_00_u03b1_4871_, lean_object* v_e_4872_, lean_object* v_maxFVars_4873_, lean_object* v_k_4874_, lean_object* v_cleanupAnnotations_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4881_; lean_object* v_res_4882_; 
v_cleanupAnnotations_boxed_4881_ = lean_unbox(v_cleanupAnnotations_4875_);
v_res_4882_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_00_u03b1_4871_, v_e_4872_, v_maxFVars_4873_, v_k_4874_, v_cleanupAnnotations_boxed_4881_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_);
lean_dec(v___y_4879_);
lean_dec_ref(v___y_4878_);
lean_dec(v___y_4877_);
lean_dec_ref(v___y_4876_);
return v_res_4882_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___y_4883_){
_start:
{
if (lean_obj_tag(v___y_4883_) == 0)
{
uint8_t v___x_4884_; 
v___x_4884_ = 1;
return v___x_4884_;
}
else
{
uint8_t v___x_4885_; 
v___x_4885_ = 0;
return v___x_4885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___y_4886_){
_start:
{
uint8_t v_res_4887_; lean_object* v_r_4888_; 
v_res_4887_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___y_4886_);
lean_dec(v___y_4886_);
v_r_4888_ = lean_box(v_res_4887_);
return v_r_4888_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2(void){
_start:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4891_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__1));
v___x_4892_ = lean_unsigned_to_nat(12u);
v___x_4893_ = lean_unsigned_to_nat(376u);
v___x_4894_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__0));
v___x_4895_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4896_ = l_mkPanicMessageWithDecl(v___x_4895_, v___x_4894_, v___x_4893_, v___x_4892_, v___x_4891_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___boxed(lean_object* v___x_4898_, lean_object* v_xs_4899_, lean_object* v_tail_4900_, lean_object* v___x_4901_, lean_object* v___x_4902_, lean_object* v_ys_4903_, lean_object* v_value_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_){
_start:
{
uint8_t v___x_1280__boxed_4910_; uint8_t v___x_1281__boxed_4911_; lean_object* v_res_4912_; 
v___x_1280__boxed_4910_ = lean_unbox(v___x_4901_);
v___x_1281__boxed_4911_ = lean_unbox(v___x_4902_);
v_res_4912_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1(v___x_4898_, v_xs_4899_, v_tail_4900_, v___x_1280__boxed_4910_, v___x_1281__boxed_4911_, v_ys_4903_, v_value_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_);
lean_dec(v___y_4908_);
lean_dec_ref(v___y_4907_);
lean_dec(v___y_4906_);
lean_dec_ref(v___y_4905_);
lean_dec_ref(v_ys_4903_);
lean_dec(v___x_4898_);
return v_res_4912_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1(void){
_start:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4913_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4914_ = lean_unsigned_to_nat(8u);
v___x_4915_ = lean_unsigned_to_nat(368u);
v___x_4916_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__0));
v___x_4917_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4918_ = l_mkPanicMessageWithDecl(v___x_4917_, v___x_4916_, v___x_4915_, v___x_4914_, v___x_4913_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4919_, lean_object* v_x_4920_, lean_object* v_x_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_){
_start:
{
if (lean_obj_tag(v_x_4920_) == 0)
{
lean_object* v___x_4927_; 
lean_dec_ref(v_xs_4919_);
v___x_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4927_, 0, v_x_4921_);
return v___x_4927_;
}
else
{
lean_object* v_head_4928_; 
v_head_4928_ = lean_ctor_get(v_x_4920_, 0);
if (lean_obj_tag(v_head_4928_) == 0)
{
lean_object* v_tail_4929_; lean_object* v___f_4930_; uint8_t v___x_4931_; 
v_tail_4929_ = lean_ctor_get(v_x_4920_, 1);
lean_inc_n(v_tail_4929_, 2);
lean_dec_ref(v_x_4920_);
v___f_4930_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0));
v___x_4931_ = l_List_all___redArg(v_tail_4929_, v___f_4930_);
if (v___x_4931_ == 0)
{
uint8_t v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___f_4936_; lean_object* v___x_4937_; 
v___x_4932_ = 1;
v___x_4933_ = lean_unsigned_to_nat(1u);
v___x_4934_ = lean_box(v___x_4931_);
v___x_4935_ = lean_box(v___x_4932_);
v___f_4936_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4936_, 0, v___x_4933_);
lean_closure_set(v___f_4936_, 1, v_xs_4919_);
lean_closure_set(v___f_4936_, 2, v_tail_4929_);
lean_closure_set(v___f_4936_, 3, v___x_4934_);
lean_closure_set(v___f_4936_, 4, v___x_4935_);
v___x_4937_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(v_x_4921_, v___x_4933_, v___f_4936_, v___x_4931_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_);
return v___x_4937_;
}
else
{
lean_object* v___x_4938_; 
lean_dec(v_tail_4929_);
lean_dec_ref(v_xs_4919_);
v___x_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4938_, 0, v_x_4921_);
return v___x_4938_;
}
}
else
{
lean_object* v_tail_4939_; lean_object* v_val_4940_; lean_object* v___x_4941_; uint8_t v___x_4942_; 
lean_inc_ref(v_head_4928_);
v_tail_4939_ = lean_ctor_get(v_x_4920_, 1);
lean_inc(v_tail_4939_);
lean_dec_ref(v_x_4920_);
v_val_4940_ = lean_ctor_get(v_head_4928_, 0);
lean_inc(v_val_4940_);
lean_dec_ref(v_head_4928_);
v___x_4941_ = lean_array_get_size(v_xs_4919_);
v___x_4942_ = lean_nat_dec_lt(v_val_4940_, v___x_4941_);
if (v___x_4942_ == 0)
{
lean_object* v___x_4943_; lean_object* v___x_4944_; 
lean_dec(v_val_4940_);
lean_dec(v_tail_4939_);
lean_dec_ref(v_x_4921_);
lean_dec_ref(v_xs_4919_);
v___x_4943_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1);
v___x_4944_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4943_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_);
return v___x_4944_;
}
else
{
lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4945_ = l_Lean_instInhabitedExpr;
v___x_4946_ = lean_array_get_borrowed(v___x_4945_, v_xs_4919_, v_val_4940_);
lean_dec(v_val_4940_);
v___x_4947_ = lean_unsigned_to_nat(1u);
v___x_4948_ = lean_mk_empty_array_with_capacity(v___x_4947_);
lean_inc(v___x_4946_);
v___x_4949_ = lean_array_push(v___x_4948_, v___x_4946_);
v___x_4950_ = l_Lean_Meta_instantiateLambda(v_x_4921_, v___x_4949_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_);
lean_dec_ref(v___x_4949_);
if (lean_obj_tag(v___x_4950_) == 0)
{
lean_object* v_a_4951_; 
v_a_4951_ = lean_ctor_get(v___x_4950_, 0);
lean_inc(v_a_4951_);
lean_dec_ref(v___x_4950_);
v_x_4920_ = v_tail_4939_;
v_x_4921_ = v_a_4951_;
goto _start;
}
else
{
lean_dec(v_tail_4939_);
lean_dec_ref(v_xs_4919_);
return v___x_4950_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1(lean_object* v___x_4953_, lean_object* v_xs_4954_, lean_object* v_tail_4955_, uint8_t v___x_4956_, uint8_t v___x_4957_, lean_object* v_ys_4958_, lean_object* v_value_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_){
_start:
{
lean_object* v___x_4965_; uint8_t v___x_4966_; 
v___x_4965_ = lean_array_get_size(v_ys_4958_);
v___x_4966_ = lean_nat_dec_eq(v___x_4965_, v___x_4953_);
if (v___x_4966_ == 0)
{
lean_object* v___x_4967_; lean_object* v___x_4968_; 
lean_dec_ref(v_value_4959_);
lean_dec(v_tail_4955_);
lean_dec_ref(v_xs_4954_);
v___x_4967_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2);
v___x_4968_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4967_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
return v___x_4968_;
}
else
{
lean_object* v___x_4969_; 
v___x_4969_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4954_, v_tail_4955_, v_value_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v_a_4970_; uint8_t v___x_4971_; lean_object* v___x_4972_; 
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
lean_inc(v_a_4970_);
lean_dec_ref(v___x_4969_);
v___x_4971_ = 1;
v___x_4972_ = l_Lean_Meta_mkLambdaFVars(v_ys_4958_, v_a_4970_, v___x_4956_, v___x_4957_, v___x_4956_, v___x_4957_, v___x_4971_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
return v___x_4972_;
}
else
{
return v___x_4969_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_4973_, lean_object* v_x_4974_, lean_object* v_x_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_){
_start:
{
lean_object* v_res_4981_; 
v_res_4981_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4973_, v_x_4974_, v_x_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
lean_dec(v_a_4977_);
lean_dec_ref(v_a_4976_);
return v_res_4981_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4983_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4984_ = lean_unsigned_to_nat(2u);
v___x_4985_ = lean_unsigned_to_nat(362u);
v___x_4986_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_4987_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_4988_ = l_mkPanicMessageWithDecl(v___x_4987_, v___x_4986_, v___x_4985_, v___x_4984_, v___x_4983_);
return v___x_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_4989_, lean_object* v_value_u2080_4990_, lean_object* v_xs_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v___x_4997_; lean_object* v___x_4998_; uint8_t v___x_4999_; 
v___x_4997_ = lean_array_get_size(v_xs_4991_);
v___x_4998_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4989_);
v___x_4999_ = lean_nat_dec_eq(v___x_4997_, v___x_4998_);
lean_dec(v___x_4998_);
if (v___x_4999_ == 0)
{
lean_object* v___x_5000_; lean_object* v___x_5001_; 
lean_dec_ref(v_xs_4991_);
lean_dec_ref(v_value_u2080_4990_);
lean_dec_ref(v_perm_4989_);
v___x_5000_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_5001_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5000_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
return v___x_5001_;
}
else
{
lean_object* v_mask_5002_; lean_object* v___x_5003_; 
v_mask_5002_ = lean_array_to_list(v_perm_4989_);
v___x_5003_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4991_, v_mask_5002_, v_value_u2080_4990_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
return v___x_5003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_5004_, lean_object* v_value_u2080_5005_, lean_object* v_xs_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_5004_, v_value_u2080_5005_, v_xs_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
lean_dec(v_a_5008_);
lean_dec_ref(v_a_5007_);
return v_res_5012_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_5020_; 
v___x_5020_ = l_Array_instInhabited(lean_box(0));
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5021_){
_start:
{
lean_object* v___f_5022_; lean_object* v___f_5023_; lean_object* v___f_5024_; lean_object* v___f_5025_; lean_object* v___f_5026_; lean_object* v___f_5027_; lean_object* v___f_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___f_5022_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5023_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5024_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5025_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5026_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5027_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5028_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5029_, 0, v___f_5022_);
lean_ctor_set(v___x_5029_, 1, v___f_5023_);
v___x_5030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5030_, 0, v___x_5029_);
lean_ctor_set(v___x_5030_, 1, v___f_5024_);
lean_ctor_set(v___x_5030_, 2, v___f_5025_);
lean_ctor_set(v___x_5030_, 3, v___f_5026_);
lean_ctor_set(v___x_5030_, 4, v___f_5027_);
v___x_5031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5030_);
lean_ctor_set(v___x_5031_, 1, v___f_5028_);
v___x_5032_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5033_ = l_instInhabitedOfMonad___redArg(v___x_5031_, v___x_5032_);
v___x_5034_ = lean_panic_fn_borrowed(v___x_5033_, v_msg_5021_);
lean_dec(v___x_5033_);
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5035_, lean_object* v_msg_5036_){
_start:
{
lean_object* v___x_5037_; 
v___x_5037_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5036_);
return v___x_5037_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5040_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5041_ = lean_unsigned_to_nat(8u);
v___x_5042_ = lean_unsigned_to_nat(394u);
v___x_5043_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5044_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5045_ = l_mkPanicMessageWithDecl(v___x_5044_, v___x_5043_, v___x_5042_, v___x_5041_, v___x_5040_);
return v___x_5045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5046_, lean_object* v_x_5047_){
_start:
{
if (lean_obj_tag(v_x_5046_) == 0)
{
return v_x_5047_;
}
else
{
lean_object* v_head_5048_; lean_object* v_fst_5049_; 
v_head_5048_ = lean_ctor_get(v_x_5046_, 0);
v_fst_5049_ = lean_ctor_get(v_head_5048_, 0);
if (lean_obj_tag(v_fst_5049_) == 0)
{
lean_object* v_tail_5050_; 
v_tail_5050_ = lean_ctor_get(v_x_5046_, 1);
lean_inc(v_tail_5050_);
lean_dec_ref(v_x_5046_);
v_x_5046_ = v_tail_5050_;
goto _start;
}
else
{
lean_object* v_tail_5052_; lean_object* v_snd_5053_; lean_object* v_val_5054_; lean_object* v___x_5055_; uint8_t v___x_5056_; 
lean_inc_ref(v_fst_5049_);
lean_inc(v_head_5048_);
v_tail_5052_ = lean_ctor_get(v_x_5046_, 1);
lean_inc(v_tail_5052_);
lean_dec_ref(v_x_5046_);
v_snd_5053_ = lean_ctor_get(v_head_5048_, 1);
lean_inc(v_snd_5053_);
lean_dec(v_head_5048_);
v_val_5054_ = lean_ctor_get(v_fst_5049_, 0);
lean_inc(v_val_5054_);
lean_dec_ref(v_fst_5049_);
v___x_5055_ = lean_array_get_size(v_x_5047_);
v___x_5056_ = lean_nat_dec_lt(v_val_5054_, v___x_5055_);
if (v___x_5056_ == 0)
{
lean_object* v___x_5057_; lean_object* v___x_5058_; 
lean_dec(v_val_5054_);
lean_dec(v_snd_5053_);
lean_dec(v_tail_5052_);
lean_dec_ref(v_x_5047_);
v___x_5057_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5058_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5057_);
return v___x_5058_;
}
else
{
lean_object* v___x_5059_; 
v___x_5059_ = lean_array_set(v_x_5047_, v_val_5054_, v_snd_5053_);
lean_dec(v_val_5054_);
v_x_5046_ = v_tail_5052_;
v_x_5047_ = v___x_5059_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5061_, lean_object* v_x_5062_, lean_object* v_x_5063_){
_start:
{
lean_object* v___x_5064_; 
v___x_5064_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5062_, v_x_5063_);
return v___x_5064_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5067_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5068_ = lean_unsigned_to_nat(2u);
v___x_5069_ = lean_unsigned_to_nat(384u);
v___x_5070_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5071_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5072_ = l_mkPanicMessageWithDecl(v___x_5071_, v___x_5070_, v___x_5069_, v___x_5068_, v___x_5067_);
return v___x_5072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5075_, lean_object* v_xs_5076_){
_start:
{
lean_object* v___x_5077_; lean_object* v___x_5078_; uint8_t v___x_5079_; 
v___x_5077_ = lean_array_get_size(v_xs_5076_);
v___x_5078_ = lean_array_get_size(v_perm_5075_);
v___x_5079_ = lean_nat_dec_eq(v___x_5077_, v___x_5078_);
if (v___x_5079_ == 0)
{
lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_5080_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5081_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5080_);
return v___x_5081_;
}
else
{
lean_object* v___x_5082_; uint8_t v___x_5083_; 
v___x_5082_ = lean_unsigned_to_nat(0u);
v___x_5083_ = lean_nat_dec_eq(v___x_5077_, v___x_5082_);
if (v___x_5083_ == 0)
{
lean_object* v_dummy_5084_; lean_object* v___x_5085_; lean_object* v_ys_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v_dummy_5084_ = lean_array_fget_borrowed(v_xs_5076_, v___x_5082_);
v___x_5085_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5075_);
lean_inc(v_dummy_5084_);
v_ys_5086_ = lean_mk_array(v___x_5085_, v_dummy_5084_);
v___x_5087_ = l_Array_zip___redArg(v_perm_5075_, v_xs_5076_);
v___x_5088_ = lean_array_to_list(v___x_5087_);
v___x_5089_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5088_, v_ys_5086_);
return v___x_5089_;
}
else
{
lean_object* v___x_5090_; 
v___x_5090_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5091_, lean_object* v_xs_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5091_, v_xs_5092_);
lean_dec_ref(v_xs_5092_);
lean_dec_ref(v_perm_5091_);
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5094_, lean_object* v_perm_5095_, lean_object* v_xs_5096_){
_start:
{
lean_object* v___x_5097_; 
v___x_5097_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5095_, v_xs_5096_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5098_, lean_object* v_perm_5099_, lean_object* v_xs_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5098_, v_perm_5099_, v_xs_5100_);
lean_dec_ref(v_xs_5100_);
lean_dec_ref(v_perm_5099_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5102_, lean_object* v_upperBound_5103_, lean_object* v_perm_5104_, lean_object* v_a_5105_, lean_object* v_b_5106_){
_start:
{
lean_object* v_a_5108_; uint8_t v___x_5115_; 
v___x_5115_ = lean_nat_dec_lt(v_a_5105_, v_upperBound_5103_);
if (v___x_5115_ == 0)
{
lean_dec(v_a_5105_);
return v_b_5106_;
}
else
{
lean_object* v___x_5116_; uint8_t v___x_5117_; 
v___x_5116_ = lean_array_get_size(v_perm_5104_);
v___x_5117_ = lean_nat_dec_lt(v_a_5105_, v___x_5116_);
if (v___x_5117_ == 0)
{
goto v___jp_5112_;
}
else
{
lean_object* v___x_5118_; 
v___x_5118_ = lean_array_fget_borrowed(v_perm_5104_, v_a_5105_);
if (lean_obj_tag(v___x_5118_) == 0)
{
goto v___jp_5112_;
}
else
{
v_a_5108_ = v_b_5106_;
goto v___jp_5107_;
}
}
}
v___jp_5107_:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5109_ = lean_unsigned_to_nat(1u);
v___x_5110_ = lean_nat_add(v_a_5105_, v___x_5109_);
lean_dec(v_a_5105_);
v_a_5105_ = v___x_5110_;
v_b_5106_ = v_a_5108_;
goto _start;
}
v___jp_5112_:
{
lean_object* v___x_5113_; lean_object* v___x_5114_; 
v___x_5113_ = lean_array_fget_borrowed(v_xs_5102_, v_a_5105_);
lean_inc(v___x_5113_);
v___x_5114_ = lean_array_push(v_b_5106_, v___x_5113_);
v_a_5108_ = v___x_5114_;
goto v___jp_5107_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5119_, lean_object* v_upperBound_5120_, lean_object* v_perm_5121_, lean_object* v_a_5122_, lean_object* v_b_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5119_, v_upperBound_5120_, v_perm_5121_, v_a_5122_, v_b_5123_);
lean_dec_ref(v_perm_5121_);
lean_dec(v_upperBound_5120_);
lean_dec_ref(v_xs_5119_);
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5125_, lean_object* v_xs_5126_){
_start:
{
lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v_ys_5129_; lean_object* v___x_5130_; 
v___x_5127_ = lean_array_get_size(v_xs_5126_);
v___x_5128_ = lean_unsigned_to_nat(0u);
v_ys_5129_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5126_, v___x_5127_, v_perm_5125_, v___x_5128_, v_ys_5129_);
return v___x_5130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5131_, lean_object* v_xs_5132_){
_start:
{
lean_object* v_res_5133_; 
v_res_5133_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5131_, v_xs_5132_);
lean_dec_ref(v_xs_5132_);
lean_dec_ref(v_perm_5131_);
return v_res_5133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5134_, lean_object* v_perm_5135_, lean_object* v_xs_5136_){
_start:
{
lean_object* v___x_5137_; 
v___x_5137_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5135_, v_xs_5136_);
return v___x_5137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5138_, lean_object* v_perm_5139_, lean_object* v_xs_5140_){
_start:
{
lean_object* v_res_5141_; 
v_res_5141_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5138_, v_perm_5139_, v_xs_5140_);
lean_dec_ref(v_xs_5140_);
lean_dec_ref(v_perm_5139_);
return v_res_5141_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5142_, lean_object* v_xs_5143_, lean_object* v_upperBound_5144_, lean_object* v_perm_5145_, lean_object* v_inst_5146_, lean_object* v_R_5147_, lean_object* v_a_5148_, lean_object* v_b_5149_, lean_object* v_c_5150_){
_start:
{
lean_object* v___x_5151_; 
v___x_5151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5143_, v_upperBound_5144_, v_perm_5145_, v_a_5148_, v_b_5149_);
return v___x_5151_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5152_, lean_object* v_xs_5153_, lean_object* v_upperBound_5154_, lean_object* v_perm_5155_, lean_object* v_inst_5156_, lean_object* v_R_5157_, lean_object* v_a_5158_, lean_object* v_b_5159_, lean_object* v_c_5160_){
_start:
{
lean_object* v_res_5161_; 
v_res_5161_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5152_, v_xs_5153_, v_upperBound_5154_, v_perm_5155_, v_inst_5156_, v_R_5157_, v_a_5158_, v_b_5159_, v_c_5160_);
lean_dec_ref(v_perm_5155_);
lean_dec(v_upperBound_5154_);
lean_dec_ref(v_xs_5153_);
return v_res_5161_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(lean_object* v_msg_5162_){
_start:
{
lean_object* v___x_5163_; lean_object* v___x_5164_; 
v___x_5163_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5164_ = lean_panic_fn_borrowed(v___x_5163_, v_msg_5162_);
return v___x_5164_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_00_u03b1_5165_, lean_object* v_msg_5166_){
_start:
{
lean_object* v___x_5167_; 
v___x_5167_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v_msg_5166_);
return v___x_5167_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_as_5168_, size_t v_i_5169_, size_t v_stop_5170_){
_start:
{
uint8_t v___x_5171_; 
v___x_5171_ = lean_usize_dec_eq(v_i_5169_, v_stop_5170_);
if (v___x_5171_ == 0)
{
uint8_t v___x_5172_; lean_object* v___x_5173_; 
v___x_5172_ = 1;
v___x_5173_ = lean_array_uget_borrowed(v_as_5168_, v_i_5169_);
if (lean_obj_tag(v___x_5173_) == 0)
{
if (v___x_5171_ == 0)
{
size_t v___x_5174_; size_t v___x_5175_; 
v___x_5174_ = ((size_t)1ULL);
v___x_5175_ = lean_usize_add(v_i_5169_, v___x_5174_);
v_i_5169_ = v___x_5175_;
goto _start;
}
else
{
return v___x_5172_;
}
}
else
{
return v___x_5172_;
}
}
else
{
uint8_t v___x_5177_; 
v___x_5177_ = 0;
return v___x_5177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___boxed(lean_object* v_as_5178_, lean_object* v_i_5179_, lean_object* v_stop_5180_){
_start:
{
size_t v_i_boxed_5181_; size_t v_stop_boxed_5182_; uint8_t v_res_5183_; lean_object* v_r_5184_; 
v_i_boxed_5181_ = lean_unbox_usize(v_i_5179_);
lean_dec(v_i_5179_);
v_stop_boxed_5182_ = lean_unbox_usize(v_stop_5180_);
lean_dec(v_stop_5180_);
v_res_5183_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v_as_5178_, v_i_boxed_5181_, v_stop_boxed_5182_);
lean_dec_ref(v_as_5178_);
v_r_5184_ = lean_box(v_res_5183_);
return v_r_5184_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; 
v___x_5187_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5188_ = lean_unsigned_to_nat(12u);
v___x_5189_ = lean_unsigned_to_nat(433u);
v___x_5190_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5191_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5192_ = l_mkPanicMessageWithDecl(v___x_5191_, v___x_5190_, v___x_5189_, v___x_5188_, v___x_5187_);
return v___x_5192_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; 
v___x_5194_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5195_ = lean_unsigned_to_nat(10u);
v___x_5196_ = lean_unsigned_to_nat(425u);
v___x_5197_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5198_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5199_ = l_mkPanicMessageWithDecl(v___x_5198_, v___x_5197_, v___x_5196_, v___x_5195_, v___x_5194_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5200_, lean_object* v_fixedArgs_5201_, lean_object* v_varyingArgs_5202_, lean_object* v_i_5203_, lean_object* v_j_5204_, lean_object* v_xs_5205_){
_start:
{
lean_object* v_lower_5207_; lean_object* v_upper_5208_; lean_object* v___y_5213_; lean_object* v___y_5214_; lean_object* v___y_5215_; lean_object* v_lower_5223_; lean_object* v_upper_5224_; lean_object* v___x_5232_; uint8_t v___x_5233_; 
v___x_5232_ = lean_array_get_size(v_perm_5200_);
v___x_5233_ = lean_nat_dec_lt(v_i_5203_, v___x_5232_);
if (v___x_5233_ == 0)
{
lean_object* v___x_5234_; lean_object* v___x_5235_; uint8_t v___x_5236_; 
lean_dec(v_i_5203_);
lean_dec_ref(v_perm_5200_);
v___x_5234_ = lean_unsigned_to_nat(0u);
v___x_5235_ = lean_array_get_size(v_varyingArgs_5202_);
v___x_5236_ = lean_nat_dec_le(v_j_5204_, v___x_5234_);
if (v___x_5236_ == 0)
{
v_lower_5207_ = v_j_5204_;
v_upper_5208_ = v___x_5235_;
goto v___jp_5206_;
}
else
{
lean_dec(v_j_5204_);
v_lower_5207_ = v___x_5234_;
v_upper_5208_ = v___x_5235_;
goto v___jp_5206_;
}
}
else
{
lean_object* v___x_5237_; 
v___x_5237_ = lean_array_fget_borrowed(v_perm_5200_, v_i_5203_);
if (lean_obj_tag(v___x_5237_) == 1)
{
lean_object* v_val_5238_; lean_object* v___x_5239_; uint8_t v___x_5240_; 
v_val_5238_ = lean_ctor_get(v___x_5237_, 0);
v___x_5239_ = lean_array_get_size(v_fixedArgs_5201_);
v___x_5240_ = lean_nat_dec_lt(v_val_5238_, v___x_5239_);
if (v___x_5240_ == 0)
{
lean_object* v___x_5241_; lean_object* v___x_5242_; 
lean_dec_ref(v_xs_5205_);
lean_dec(v_j_5204_);
lean_dec(v_i_5203_);
lean_dec_ref(v_varyingArgs_5202_);
lean_dec_ref(v_perm_5200_);
v___x_5241_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5242_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5241_);
return v___x_5242_;
}
else
{
lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5243_ = lean_unsigned_to_nat(1u);
v___x_5244_ = lean_nat_add(v_i_5203_, v___x_5243_);
lean_dec(v_i_5203_);
v___x_5245_ = lean_array_fget_borrowed(v_fixedArgs_5201_, v_val_5238_);
lean_inc(v___x_5245_);
v___x_5246_ = lean_array_push(v_xs_5205_, v___x_5245_);
v_i_5203_ = v___x_5244_;
v_xs_5205_ = v___x_5246_;
goto _start;
}
}
else
{
lean_object* v___x_5248_; uint8_t v___x_5249_; 
v___x_5248_ = lean_array_get_size(v_varyingArgs_5202_);
v___x_5249_ = lean_nat_dec_lt(v_j_5204_, v___x_5248_);
if (v___x_5249_ == 0)
{
lean_object* v___x_5250_; uint8_t v___x_5251_; 
lean_dec(v_j_5204_);
lean_dec_ref(v_varyingArgs_5202_);
v___x_5250_ = lean_unsigned_to_nat(0u);
v___x_5251_ = lean_nat_dec_le(v_i_5203_, v___x_5250_);
if (v___x_5251_ == 0)
{
v_lower_5223_ = v_i_5203_;
v_upper_5224_ = v___x_5232_;
goto v___jp_5222_;
}
else
{
lean_dec(v_i_5203_);
v_lower_5223_ = v___x_5250_;
v_upper_5224_ = v___x_5232_;
goto v___jp_5222_;
}
}
else
{
lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; 
v___x_5252_ = lean_unsigned_to_nat(1u);
v___x_5253_ = lean_nat_add(v_i_5203_, v___x_5252_);
lean_dec(v_i_5203_);
v___x_5254_ = lean_nat_add(v_j_5204_, v___x_5252_);
v___x_5255_ = lean_array_fget_borrowed(v_varyingArgs_5202_, v_j_5204_);
lean_dec(v_j_5204_);
lean_inc(v___x_5255_);
v___x_5256_ = lean_array_push(v_xs_5205_, v___x_5255_);
v_i_5203_ = v___x_5253_;
v_j_5204_ = v___x_5254_;
v_xs_5205_ = v___x_5256_;
goto _start;
}
}
}
v___jp_5206_:
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; 
v___x_5209_ = l_Array_toSubarray___redArg(v_varyingArgs_5202_, v_lower_5207_, v_upper_5208_);
v___x_5210_ = l_Subarray_copy___redArg(v___x_5209_);
v___x_5211_ = l_Array_append___redArg(v_xs_5205_, v___x_5210_);
lean_dec_ref(v___x_5210_);
return v___x_5211_;
}
v___jp_5212_:
{
uint8_t v___x_5216_; 
v___x_5216_ = lean_nat_dec_lt(v___y_5214_, v___y_5215_);
if (v___x_5216_ == 0)
{
lean_dec(v___y_5215_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
return v_xs_5205_;
}
else
{
size_t v___x_5217_; size_t v___x_5218_; uint8_t v___x_5219_; 
v___x_5217_ = lean_usize_of_nat(v___y_5214_);
lean_dec(v___y_5214_);
v___x_5218_ = lean_usize_of_nat(v___y_5215_);
lean_dec(v___y_5215_);
v___x_5219_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v___y_5213_, v___x_5217_, v___x_5218_);
lean_dec_ref(v___y_5213_);
if (v___x_5219_ == 0)
{
return v_xs_5205_;
}
else
{
lean_object* v___x_5220_; lean_object* v___x_5221_; 
lean_dec_ref(v_xs_5205_);
v___x_5220_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5221_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5220_);
return v___x_5221_;
}
}
}
v___jp_5222_:
{
lean_object* v___x_5225_; lean_object* v_array_5226_; lean_object* v_start_5227_; lean_object* v_stop_5228_; uint8_t v___x_5229_; 
v___x_5225_ = l_Array_toSubarray___redArg(v_perm_5200_, v_lower_5223_, v_upper_5224_);
v_array_5226_ = lean_ctor_get(v___x_5225_, 0);
lean_inc_ref(v_array_5226_);
v_start_5227_ = lean_ctor_get(v___x_5225_, 1);
lean_inc(v_start_5227_);
v_stop_5228_ = lean_ctor_get(v___x_5225_, 2);
lean_inc(v_stop_5228_);
lean_dec_ref(v___x_5225_);
v___x_5229_ = lean_nat_dec_lt(v_start_5227_, v_stop_5228_);
if (v___x_5229_ == 0)
{
lean_dec(v_stop_5228_);
lean_dec(v_start_5227_);
lean_dec_ref(v_array_5226_);
return v_xs_5205_;
}
else
{
lean_object* v___x_5230_; uint8_t v___x_5231_; 
v___x_5230_ = lean_array_get_size(v_array_5226_);
v___x_5231_ = lean_nat_dec_le(v_stop_5228_, v___x_5230_);
if (v___x_5231_ == 0)
{
lean_dec(v_stop_5228_);
v___y_5213_ = v_array_5226_;
v___y_5214_ = v_start_5227_;
v___y_5215_ = v___x_5230_;
goto v___jp_5212_;
}
else
{
v___y_5213_ = v_array_5226_;
v___y_5214_ = v_start_5227_;
v___y_5215_ = v_stop_5228_;
goto v___jp_5212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5258_, lean_object* v_fixedArgs_5259_, lean_object* v_varyingArgs_5260_, lean_object* v_i_5261_, lean_object* v_j_5262_, lean_object* v_xs_5263_){
_start:
{
lean_object* v_res_5264_; 
v_res_5264_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5258_, v_fixedArgs_5259_, v_varyingArgs_5260_, v_i_5261_, v_j_5262_, v_xs_5263_);
lean_dec_ref(v_fixedArgs_5259_);
return v_res_5264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5265_, lean_object* v_perm_5266_, lean_object* v_fixedArgs_5267_, lean_object* v_varyingArgs_5268_, lean_object* v_i_5269_, lean_object* v_j_5270_, lean_object* v_xs_5271_){
_start:
{
lean_object* v___x_5272_; 
v___x_5272_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5266_, v_fixedArgs_5267_, v_varyingArgs_5268_, v_i_5269_, v_j_5270_, v_xs_5271_);
return v___x_5272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5273_, lean_object* v_perm_5274_, lean_object* v_fixedArgs_5275_, lean_object* v_varyingArgs_5276_, lean_object* v_i_5277_, lean_object* v_j_5278_, lean_object* v_xs_5279_){
_start:
{
lean_object* v_res_5280_; 
v_res_5280_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5273_, v_perm_5274_, v_fixedArgs_5275_, v_varyingArgs_5276_, v_i_5277_, v_j_5278_, v_xs_5279_);
lean_dec_ref(v_fixedArgs_5275_);
return v_res_5280_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5283_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5284_ = lean_unsigned_to_nat(2u);
v___x_5285_ = lean_unsigned_to_nat(416u);
v___x_5286_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5287_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5288_ = l_mkPanicMessageWithDecl(v___x_5287_, v___x_5286_, v___x_5285_, v___x_5284_, v___x_5283_);
return v___x_5288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5289_, lean_object* v_fixedArgs_5290_, lean_object* v_varyingArgs_5291_){
_start:
{
lean_object* v___x_5292_; lean_object* v___x_5293_; uint8_t v___x_5294_; 
v___x_5292_ = lean_array_get_size(v_fixedArgs_5290_);
v___x_5293_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5289_);
v___x_5294_ = lean_nat_dec_eq(v___x_5292_, v___x_5293_);
lean_dec(v___x_5293_);
if (v___x_5294_ == 0)
{
lean_object* v___x_5295_; lean_object* v___x_5296_; 
lean_dec_ref(v_varyingArgs_5291_);
lean_dec_ref(v_perm_5289_);
v___x_5295_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5296_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5295_);
return v___x_5296_;
}
else
{
lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; 
v___x_5297_ = lean_unsigned_to_nat(0u);
v___x_5298_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5299_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5289_, v_fixedArgs_5290_, v_varyingArgs_5291_, v___x_5297_, v___x_5297_, v___x_5298_);
return v___x_5299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5300_, lean_object* v_fixedArgs_5301_, lean_object* v_varyingArgs_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5300_, v_fixedArgs_5301_, v_varyingArgs_5302_);
lean_dec_ref(v_fixedArgs_5301_);
return v_res_5303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5304_, lean_object* v_perm_5305_, lean_object* v_fixedArgs_5306_, lean_object* v_varyingArgs_5307_){
_start:
{
lean_object* v___x_5308_; 
v___x_5308_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5305_, v_fixedArgs_5306_, v_varyingArgs_5307_);
return v___x_5308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5309_, lean_object* v_perm_5310_, lean_object* v_fixedArgs_5311_, lean_object* v_varyingArgs_5312_){
_start:
{
lean_object* v_res_5313_; 
v_res_5313_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5309_, v_perm_5310_, v_fixedArgs_5311_, v_varyingArgs_5312_);
lean_dec_ref(v_fixedArgs_5311_);
return v_res_5313_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5314_, lean_object* v_x_5315_){
_start:
{
if (lean_obj_tag(v_x_5314_) == 0)
{
if (lean_obj_tag(v_x_5315_) == 0)
{
uint8_t v___x_5316_; 
v___x_5316_ = 1;
return v___x_5316_;
}
else
{
uint8_t v___x_5317_; 
v___x_5317_ = 0;
return v___x_5317_;
}
}
else
{
if (lean_obj_tag(v_x_5315_) == 0)
{
uint8_t v___x_5318_; 
v___x_5318_ = 0;
return v___x_5318_;
}
else
{
lean_object* v_val_5319_; lean_object* v_val_5320_; uint8_t v___x_5321_; 
v_val_5319_ = lean_ctor_get(v_x_5314_, 0);
v_val_5320_ = lean_ctor_get(v_x_5315_, 0);
v___x_5321_ = lean_nat_dec_eq(v_val_5319_, v_val_5320_);
return v___x_5321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5322_, lean_object* v_x_5323_){
_start:
{
uint8_t v_res_5324_; lean_object* v_r_5325_; 
v_res_5324_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5322_, v_x_5323_);
lean_dec(v_x_5323_);
lean_dec(v_x_5322_);
v_r_5325_ = lean_box(v_res_5324_);
return v_r_5325_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5326_, lean_object* v_ys_5327_, lean_object* v_x_5328_){
_start:
{
lean_object* v_zero_5329_; uint8_t v_isZero_5330_; 
v_zero_5329_ = lean_unsigned_to_nat(0u);
v_isZero_5330_ = lean_nat_dec_eq(v_x_5328_, v_zero_5329_);
if (v_isZero_5330_ == 1)
{
lean_dec(v_x_5328_);
return v_isZero_5330_;
}
else
{
lean_object* v_one_5331_; lean_object* v_n_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; uint8_t v___x_5335_; 
v_one_5331_ = lean_unsigned_to_nat(1u);
v_n_5332_ = lean_nat_sub(v_x_5328_, v_one_5331_);
lean_dec(v_x_5328_);
v___x_5333_ = lean_array_fget_borrowed(v_xs_5326_, v_n_5332_);
v___x_5334_ = lean_array_fget_borrowed(v_ys_5327_, v_n_5332_);
v___x_5335_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5333_, v___x_5334_);
if (v___x_5335_ == 0)
{
lean_dec(v_n_5332_);
return v___x_5335_;
}
else
{
v_x_5328_ = v_n_5332_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5337_, lean_object* v_ys_5338_, lean_object* v_x_5339_){
_start:
{
uint8_t v_res_5340_; lean_object* v_r_5341_; 
v_res_5340_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5337_, v_ys_5338_, v_x_5339_);
lean_dec_ref(v_ys_5338_);
lean_dec_ref(v_xs_5337_);
v_r_5341_ = lean_box(v_res_5340_);
return v_r_5341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5342_, size_t v_i_5343_, lean_object* v_bs_5344_){
_start:
{
uint8_t v___x_5345_; 
v___x_5345_ = lean_usize_dec_lt(v_i_5343_, v_sz_5342_);
if (v___x_5345_ == 0)
{
return v_bs_5344_;
}
else
{
lean_object* v_v_5346_; lean_object* v___x_5347_; lean_object* v_bs_x27_5348_; lean_object* v___x_5349_; size_t v___x_5350_; size_t v___x_5351_; lean_object* v___x_5352_; 
v_v_5346_ = lean_array_uget(v_bs_5344_, v_i_5343_);
v___x_5347_ = lean_unsigned_to_nat(0u);
v_bs_x27_5348_ = lean_array_uset(v_bs_5344_, v_i_5343_, v___x_5347_);
v___x_5349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5349_, 0, v_v_5346_);
v___x_5350_ = ((size_t)1ULL);
v___x_5351_ = lean_usize_add(v_i_5343_, v___x_5350_);
v___x_5352_ = lean_array_uset(v_bs_x27_5348_, v_i_5343_, v___x_5349_);
v_i_5343_ = v___x_5351_;
v_bs_5344_ = v___x_5352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5354_, lean_object* v_i_5355_, lean_object* v_bs_5356_){
_start:
{
size_t v_sz_boxed_5357_; size_t v_i_boxed_5358_; lean_object* v_res_5359_; 
v_sz_boxed_5357_ = lean_unbox_usize(v_sz_5354_);
lean_dec(v_sz_5354_);
v_i_boxed_5358_ = lean_unbox_usize(v_i_5355_);
lean_dec(v_i_5355_);
v_res_5359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5357_, v_i_boxed_5358_, v_bs_5356_);
return v_res_5359_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5360_, lean_object* v_as_5361_, size_t v_i_5362_, size_t v_stop_5363_){
_start:
{
uint8_t v___x_5364_; 
v___x_5364_ = lean_usize_dec_eq(v_i_5362_, v_stop_5363_);
if (v___x_5364_ == 0)
{
lean_object* v_numFixed_5365_; uint8_t v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; size_t v_sz_5369_; size_t v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; uint8_t v___x_5378_; 
v_numFixed_5365_ = lean_ctor_get(v_fixedParamPerms_5360_, 0);
v___x_5366_ = 1;
v___x_5367_ = lean_array_uget_borrowed(v_as_5361_, v_i_5362_);
lean_inc(v_numFixed_5365_);
v___x_5368_ = l_Array_range(v_numFixed_5365_);
v_sz_5369_ = lean_array_size(v___x_5368_);
v___x_5370_ = ((size_t)0ULL);
v___x_5371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5369_, v___x_5370_, v___x_5368_);
v___x_5372_ = lean_array_get_size(v___x_5367_);
v___x_5373_ = lean_nat_sub(v___x_5372_, v_numFixed_5365_);
v___x_5374_ = lean_box(0);
v___x_5375_ = lean_mk_array(v___x_5373_, v___x_5374_);
v___x_5376_ = l_Array_append___redArg(v___x_5371_, v___x_5375_);
lean_dec_ref(v___x_5375_);
v___x_5377_ = lean_array_get_size(v___x_5376_);
v___x_5378_ = lean_nat_dec_eq(v___x_5372_, v___x_5377_);
if (v___x_5378_ == 0)
{
lean_dec_ref(v___x_5376_);
lean_dec_ref(v_fixedParamPerms_5360_);
return v___x_5366_;
}
else
{
uint8_t v___x_5379_; 
v___x_5379_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5367_, v___x_5376_, v___x_5372_);
lean_dec_ref(v___x_5376_);
if (v___x_5379_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5360_);
return v___x_5366_;
}
else
{
if (v___x_5364_ == 0)
{
size_t v___x_5380_; size_t v___x_5381_; 
v___x_5380_ = ((size_t)1ULL);
v___x_5381_ = lean_usize_add(v_i_5362_, v___x_5380_);
v_i_5362_ = v___x_5381_;
goto _start;
}
else
{
lean_dec_ref(v_fixedParamPerms_5360_);
return v___x_5366_;
}
}
}
}
else
{
uint8_t v___x_5383_; 
lean_dec_ref(v_fixedParamPerms_5360_);
v___x_5383_ = 0;
return v___x_5383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5384_, lean_object* v_as_5385_, lean_object* v_i_5386_, lean_object* v_stop_5387_){
_start:
{
size_t v_i_boxed_5388_; size_t v_stop_boxed_5389_; uint8_t v_res_5390_; lean_object* v_r_5391_; 
v_i_boxed_5388_ = lean_unbox_usize(v_i_5386_);
lean_dec(v_i_5386_);
v_stop_boxed_5389_ = lean_unbox_usize(v_stop_5387_);
lean_dec(v_stop_5387_);
v_res_5390_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5384_, v_as_5385_, v_i_boxed_5388_, v_stop_boxed_5389_);
lean_dec_ref(v_as_5385_);
v_r_5391_ = lean_box(v_res_5390_);
return v_r_5391_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5392_){
_start:
{
lean_object* v_perms_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; uint8_t v___x_5396_; 
v_perms_5393_ = lean_ctor_get(v_fixedParamPerms_5392_, 1);
lean_inc_ref(v_perms_5393_);
v___x_5394_ = lean_unsigned_to_nat(0u);
v___x_5395_ = lean_array_get_size(v_perms_5393_);
v___x_5396_ = lean_nat_dec_lt(v___x_5394_, v___x_5395_);
if (v___x_5396_ == 0)
{
uint8_t v___x_5397_; 
lean_dec_ref(v_perms_5393_);
lean_dec_ref(v_fixedParamPerms_5392_);
v___x_5397_ = 1;
return v___x_5397_;
}
else
{
if (v___x_5396_ == 0)
{
lean_dec_ref(v_perms_5393_);
lean_dec_ref(v_fixedParamPerms_5392_);
return v___x_5396_;
}
else
{
size_t v___x_5398_; size_t v___x_5399_; uint8_t v___x_5400_; 
v___x_5398_ = ((size_t)0ULL);
v___x_5399_ = lean_usize_of_nat(v___x_5395_);
v___x_5400_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5392_, v_perms_5393_, v___x_5398_, v___x_5399_);
lean_dec_ref(v_perms_5393_);
if (v___x_5400_ == 0)
{
return v___x_5396_;
}
else
{
uint8_t v___x_5401_; 
v___x_5401_ = 0;
return v___x_5401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5402_){
_start:
{
uint8_t v_res_5403_; lean_object* v_r_5404_; 
v_res_5403_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5402_);
v_r_5404_ = lean_box(v_res_5403_);
return v_r_5404_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5405_, lean_object* v_ys_5406_, lean_object* v_hsz_5407_, lean_object* v_x_5408_, lean_object* v_x_5409_){
_start:
{
uint8_t v___x_5410_; 
v___x_5410_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5405_, v_ys_5406_, v_x_5408_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5411_, lean_object* v_ys_5412_, lean_object* v_hsz_5413_, lean_object* v_x_5414_, lean_object* v_x_5415_){
_start:
{
uint8_t v_res_5416_; lean_object* v_r_5417_; 
v_res_5416_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5411_, v_ys_5412_, v_hsz_5413_, v_x_5414_, v_x_5415_);
lean_dec_ref(v_ys_5412_);
lean_dec_ref(v_xs_5411_);
v_r_5417_ = lean_box(v_res_5416_);
return v_r_5417_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5418_; 
v___x_5418_ = l_Array_instInhabited(lean_box(0));
return v___x_5418_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5419_){
_start:
{
lean_object* v___f_5420_; lean_object* v___f_5421_; lean_object* v___f_5422_; lean_object* v___f_5423_; lean_object* v___f_5424_; lean_object* v___f_5425_; lean_object* v___f_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___f_5420_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5421_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5422_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5423_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5424_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5425_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5426_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5427_, 0, v___f_5420_);
lean_ctor_set(v___x_5427_, 1, v___f_5421_);
v___x_5428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5428_, 0, v___x_5427_);
lean_ctor_set(v___x_5428_, 1, v___f_5422_);
lean_ctor_set(v___x_5428_, 2, v___f_5423_);
lean_ctor_set(v___x_5428_, 3, v___f_5424_);
lean_ctor_set(v___x_5428_, 4, v___f_5425_);
v___x_5429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5429_, 0, v___x_5428_);
lean_ctor_set(v___x_5429_, 1, v___f_5426_);
v___x_5430_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5431_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5431_);
lean_ctor_set(v___x_5432_, 1, v___x_5431_);
v___x_5433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5433_, 0, v___x_5430_);
lean_ctor_set(v___x_5433_, 1, v___x_5432_);
v___x_5434_ = l_instInhabitedOfMonad___redArg(v___x_5429_, v___x_5433_);
v___x_5435_ = lean_panic_fn_borrowed(v___x_5434_, v_msg_5419_);
lean_dec(v___x_5434_);
return v___x_5435_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5436_; 
v___x_5436_ = l_Array_instInhabited(lean_box(0));
return v___x_5436_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5437_){
_start:
{
lean_object* v___f_5438_; lean_object* v___f_5439_; lean_object* v___f_5440_; lean_object* v___f_5441_; lean_object* v___f_5442_; lean_object* v___f_5443_; lean_object* v___f_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; 
v___f_5438_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5439_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5440_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5441_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5442_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5443_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5444_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5445_, 0, v___f_5438_);
lean_ctor_set(v___x_5445_, 1, v___f_5439_);
v___x_5446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5446_, 0, v___x_5445_);
lean_ctor_set(v___x_5446_, 1, v___f_5440_);
lean_ctor_set(v___x_5446_, 2, v___f_5441_);
lean_ctor_set(v___x_5446_, 3, v___f_5442_);
lean_ctor_set(v___x_5446_, 4, v___f_5443_);
v___x_5447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5447_, 0, v___x_5446_);
lean_ctor_set(v___x_5447_, 1, v___f_5444_);
v___x_5448_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5449_, 0, v___x_5448_);
v___x_5450_ = l_instInhabitedOfMonad___redArg(v___x_5447_, v___x_5449_);
v___x_5451_ = lean_panic_fn_borrowed(v___x_5450_, v_msg_5437_);
lean_dec(v___x_5450_);
return v___x_5451_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5452_, lean_object* v_a_5453_, lean_object* v_b_5454_){
_start:
{
lean_object* v_a_5456_; uint8_t v___x_5460_; 
v___x_5460_ = lean_nat_dec_lt(v_a_5453_, v_upperBound_5452_);
if (v___x_5460_ == 0)
{
lean_dec(v_a_5453_);
return v_b_5454_;
}
else
{
lean_object* v_snd_5461_; lean_object* v_snd_5462_; lean_object* v_snd_5463_; lean_object* v_snd_5464_; lean_object* v_fst_5465_; lean_object* v___x_5467_; uint8_t v_isShared_5468_; uint8_t v_isSharedCheck_5577_; 
v_snd_5461_ = lean_ctor_get(v_b_5454_, 1);
lean_inc(v_snd_5461_);
v_snd_5462_ = lean_ctor_get(v_snd_5461_, 1);
lean_inc(v_snd_5462_);
v_snd_5463_ = lean_ctor_get(v_snd_5462_, 1);
lean_inc(v_snd_5463_);
v_snd_5464_ = lean_ctor_get(v_snd_5463_, 1);
lean_inc(v_snd_5464_);
v_fst_5465_ = lean_ctor_get(v_b_5454_, 0);
v_isSharedCheck_5577_ = !lean_is_exclusive(v_b_5454_);
if (v_isSharedCheck_5577_ == 0)
{
lean_object* v_unused_5578_; 
v_unused_5578_ = lean_ctor_get(v_b_5454_, 1);
lean_dec(v_unused_5578_);
v___x_5467_ = v_b_5454_;
v_isShared_5468_ = v_isSharedCheck_5577_;
goto v_resetjp_5466_;
}
else
{
lean_inc(v_fst_5465_);
lean_dec(v_b_5454_);
v___x_5467_ = lean_box(0);
v_isShared_5468_ = v_isSharedCheck_5577_;
goto v_resetjp_5466_;
}
v_resetjp_5466_:
{
lean_object* v_fst_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5575_; 
v_fst_5469_ = lean_ctor_get(v_snd_5461_, 0);
v_isSharedCheck_5575_ = !lean_is_exclusive(v_snd_5461_);
if (v_isSharedCheck_5575_ == 0)
{
lean_object* v_unused_5576_; 
v_unused_5576_ = lean_ctor_get(v_snd_5461_, 1);
lean_dec(v_unused_5576_);
v___x_5471_ = v_snd_5461_;
v_isShared_5472_ = v_isSharedCheck_5575_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_fst_5469_);
lean_dec(v_snd_5461_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5575_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v_fst_5473_; lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5573_; 
v_fst_5473_ = lean_ctor_get(v_snd_5462_, 0);
v_isSharedCheck_5573_ = !lean_is_exclusive(v_snd_5462_);
if (v_isSharedCheck_5573_ == 0)
{
lean_object* v_unused_5574_; 
v_unused_5574_ = lean_ctor_get(v_snd_5462_, 1);
lean_dec(v_unused_5574_);
v___x_5475_ = v_snd_5462_;
v_isShared_5476_ = v_isSharedCheck_5573_;
goto v_resetjp_5474_;
}
else
{
lean_inc(v_fst_5473_);
lean_dec(v_snd_5462_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5573_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v_fst_5477_; lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5571_; 
v_fst_5477_ = lean_ctor_get(v_snd_5463_, 0);
v_isSharedCheck_5571_ = !lean_is_exclusive(v_snd_5463_);
if (v_isSharedCheck_5571_ == 0)
{
lean_object* v_unused_5572_; 
v_unused_5572_ = lean_ctor_get(v_snd_5463_, 1);
lean_dec(v_unused_5572_);
v___x_5479_ = v_snd_5463_;
v_isShared_5480_ = v_isSharedCheck_5571_;
goto v_resetjp_5478_;
}
else
{
lean_inc(v_fst_5477_);
lean_dec(v_snd_5463_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5571_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v_array_5481_; lean_object* v_start_5482_; lean_object* v_stop_5483_; uint8_t v___x_5484_; 
v_array_5481_ = lean_ctor_get(v_snd_5464_, 0);
v_start_5482_ = lean_ctor_get(v_snd_5464_, 1);
v_stop_5483_ = lean_ctor_get(v_snd_5464_, 2);
v___x_5484_ = lean_nat_dec_lt(v_start_5482_, v_stop_5483_);
if (v___x_5484_ == 0)
{
lean_object* v___x_5486_; 
lean_dec(v_a_5453_);
if (v_isShared_5480_ == 0)
{
v___x_5486_ = v___x_5479_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v_fst_5477_);
lean_ctor_set(v_reuseFailAlloc_5496_, 1, v_snd_5464_);
v___x_5486_ = v_reuseFailAlloc_5496_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
lean_object* v___x_5488_; 
if (v_isShared_5476_ == 0)
{
lean_ctor_set(v___x_5475_, 1, v___x_5486_);
v___x_5488_ = v___x_5475_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v_fst_5473_);
lean_ctor_set(v_reuseFailAlloc_5495_, 1, v___x_5486_);
v___x_5488_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
lean_object* v___x_5490_; 
if (v_isShared_5472_ == 0)
{
lean_ctor_set(v___x_5471_, 1, v___x_5488_);
v___x_5490_ = v___x_5471_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5494_; 
v_reuseFailAlloc_5494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5494_, 0, v_fst_5469_);
lean_ctor_set(v_reuseFailAlloc_5494_, 1, v___x_5488_);
v___x_5490_ = v_reuseFailAlloc_5494_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
lean_object* v___x_5492_; 
if (v_isShared_5468_ == 0)
{
lean_ctor_set(v___x_5467_, 1, v___x_5490_);
v___x_5492_ = v___x_5467_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_fst_5465_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v___x_5490_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
}
}
else
{
lean_object* v___x_5498_; uint8_t v_isShared_5499_; uint8_t v_isSharedCheck_5567_; 
lean_inc(v_stop_5483_);
lean_inc(v_start_5482_);
lean_inc_ref(v_array_5481_);
v_isSharedCheck_5567_ = !lean_is_exclusive(v_snd_5464_);
if (v_isSharedCheck_5567_ == 0)
{
lean_object* v_unused_5568_; lean_object* v_unused_5569_; lean_object* v_unused_5570_; 
v_unused_5568_ = lean_ctor_get(v_snd_5464_, 2);
lean_dec(v_unused_5568_);
v_unused_5569_ = lean_ctor_get(v_snd_5464_, 1);
lean_dec(v_unused_5569_);
v_unused_5570_ = lean_ctor_get(v_snd_5464_, 0);
lean_dec(v_unused_5570_);
v___x_5498_ = v_snd_5464_;
v_isShared_5499_ = v_isSharedCheck_5567_;
goto v_resetjp_5497_;
}
else
{
lean_dec(v_snd_5464_);
v___x_5498_ = lean_box(0);
v_isShared_5499_ = v_isSharedCheck_5567_;
goto v_resetjp_5497_;
}
v_resetjp_5497_:
{
lean_object* v_array_5500_; lean_object* v_start_5501_; lean_object* v_stop_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5507_; 
v_array_5500_ = lean_ctor_get(v_fst_5477_, 0);
v_start_5501_ = lean_ctor_get(v_fst_5477_, 1);
v_stop_5502_ = lean_ctor_get(v_fst_5477_, 2);
v___x_5503_ = lean_array_fget(v_array_5481_, v_start_5482_);
v___x_5504_ = lean_unsigned_to_nat(1u);
v___x_5505_ = lean_nat_add(v_start_5482_, v___x_5504_);
lean_dec(v_start_5482_);
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 1, v___x_5505_);
v___x_5507_ = v___x_5498_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_array_5481_);
lean_ctor_set(v_reuseFailAlloc_5566_, 1, v___x_5505_);
lean_ctor_set(v_reuseFailAlloc_5566_, 2, v_stop_5483_);
v___x_5507_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
uint8_t v___x_5508_; 
v___x_5508_ = lean_nat_dec_lt(v_start_5501_, v_stop_5502_);
if (v___x_5508_ == 0)
{
lean_object* v___x_5510_; 
lean_dec(v___x_5503_);
lean_dec(v_a_5453_);
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 1, v___x_5507_);
v___x_5510_ = v___x_5479_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_fst_5477_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v___x_5507_);
v___x_5510_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
lean_object* v___x_5512_; 
if (v_isShared_5476_ == 0)
{
lean_ctor_set(v___x_5475_, 1, v___x_5510_);
v___x_5512_ = v___x_5475_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_fst_5473_);
lean_ctor_set(v_reuseFailAlloc_5519_, 1, v___x_5510_);
v___x_5512_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
lean_object* v___x_5514_; 
if (v_isShared_5472_ == 0)
{
lean_ctor_set(v___x_5471_, 1, v___x_5512_);
v___x_5514_ = v___x_5471_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_fst_5469_);
lean_ctor_set(v_reuseFailAlloc_5518_, 1, v___x_5512_);
v___x_5514_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
lean_object* v___x_5516_; 
if (v_isShared_5468_ == 0)
{
lean_ctor_set(v___x_5467_, 1, v___x_5514_);
v___x_5516_ = v___x_5467_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_fst_5465_);
lean_ctor_set(v_reuseFailAlloc_5517_, 1, v___x_5514_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
return v___x_5516_;
}
}
}
}
}
else
{
lean_object* v___x_5522_; uint8_t v_isShared_5523_; uint8_t v_isSharedCheck_5562_; 
lean_inc(v_stop_5502_);
lean_inc(v_start_5501_);
lean_inc_ref(v_array_5500_);
v_isSharedCheck_5562_ = !lean_is_exclusive(v_fst_5477_);
if (v_isSharedCheck_5562_ == 0)
{
lean_object* v_unused_5563_; lean_object* v_unused_5564_; lean_object* v_unused_5565_; 
v_unused_5563_ = lean_ctor_get(v_fst_5477_, 2);
lean_dec(v_unused_5563_);
v_unused_5564_ = lean_ctor_get(v_fst_5477_, 1);
lean_dec(v_unused_5564_);
v_unused_5565_ = lean_ctor_get(v_fst_5477_, 0);
lean_dec(v_unused_5565_);
v___x_5522_ = v_fst_5477_;
v_isShared_5523_ = v_isSharedCheck_5562_;
goto v_resetjp_5521_;
}
else
{
lean_dec(v_fst_5477_);
v___x_5522_ = lean_box(0);
v_isShared_5523_ = v_isSharedCheck_5562_;
goto v_resetjp_5521_;
}
v_resetjp_5521_:
{
lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5527_; 
v___x_5524_ = lean_array_fget(v_array_5500_, v_start_5501_);
v___x_5525_ = lean_nat_add(v_start_5501_, v___x_5504_);
lean_dec(v_start_5501_);
if (v_isShared_5523_ == 0)
{
lean_ctor_set(v___x_5522_, 1, v___x_5525_);
v___x_5527_ = v___x_5522_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_array_5500_);
lean_ctor_set(v_reuseFailAlloc_5561_, 1, v___x_5525_);
lean_ctor_set(v_reuseFailAlloc_5561_, 2, v_stop_5502_);
v___x_5527_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
uint8_t v___x_5528_; 
v___x_5528_ = lean_unbox(v___x_5524_);
lean_dec(v___x_5524_);
if (v___x_5528_ == 0)
{
lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5534_; 
v___x_5529_ = lean_array_get_size(v_fst_5473_);
v___x_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5530_, 0, v___x_5529_);
v___x_5531_ = lean_array_push(v_fst_5465_, v___x_5530_);
v___x_5532_ = lean_array_push(v_fst_5473_, v___x_5503_);
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 1, v___x_5507_);
lean_ctor_set(v___x_5479_, 0, v___x_5527_);
v___x_5534_ = v___x_5479_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v___x_5527_);
lean_ctor_set(v_reuseFailAlloc_5544_, 1, v___x_5507_);
v___x_5534_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
lean_object* v___x_5536_; 
if (v_isShared_5476_ == 0)
{
lean_ctor_set(v___x_5475_, 1, v___x_5534_);
lean_ctor_set(v___x_5475_, 0, v___x_5532_);
v___x_5536_ = v___x_5475_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5543_, 1, v___x_5534_);
v___x_5536_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
lean_object* v___x_5538_; 
if (v_isShared_5472_ == 0)
{
lean_ctor_set(v___x_5471_, 1, v___x_5536_);
v___x_5538_ = v___x_5471_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_fst_5469_);
lean_ctor_set(v_reuseFailAlloc_5542_, 1, v___x_5536_);
v___x_5538_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
lean_object* v___x_5540_; 
if (v_isShared_5468_ == 0)
{
lean_ctor_set(v___x_5467_, 1, v___x_5538_);
lean_ctor_set(v___x_5467_, 0, v___x_5531_);
v___x_5540_ = v___x_5467_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v___x_5531_);
lean_ctor_set(v_reuseFailAlloc_5541_, 1, v___x_5538_);
v___x_5540_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
v_a_5456_ = v___x_5540_;
goto v___jp_5455_;
}
}
}
}
}
else
{
lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5550_; 
v___x_5545_ = lean_box(0);
v___x_5546_ = lean_array_push(v_fst_5465_, v___x_5545_);
v___x_5547_ = l_Lean_Expr_fvarId_x21(v___x_5503_);
lean_dec(v___x_5503_);
v___x_5548_ = lean_array_push(v_fst_5469_, v___x_5547_);
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 1, v___x_5507_);
lean_ctor_set(v___x_5479_, 0, v___x_5527_);
v___x_5550_ = v___x_5479_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v___x_5527_);
lean_ctor_set(v_reuseFailAlloc_5560_, 1, v___x_5507_);
v___x_5550_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
lean_object* v___x_5552_; 
if (v_isShared_5476_ == 0)
{
lean_ctor_set(v___x_5475_, 1, v___x_5550_);
v___x_5552_ = v___x_5475_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v_fst_5473_);
lean_ctor_set(v_reuseFailAlloc_5559_, 1, v___x_5550_);
v___x_5552_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
lean_object* v___x_5554_; 
if (v_isShared_5472_ == 0)
{
lean_ctor_set(v___x_5471_, 1, v___x_5552_);
lean_ctor_set(v___x_5471_, 0, v___x_5548_);
v___x_5554_ = v___x_5471_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5558_, 1, v___x_5552_);
v___x_5554_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
lean_object* v___x_5556_; 
if (v_isShared_5468_ == 0)
{
lean_ctor_set(v___x_5467_, 1, v___x_5554_);
lean_ctor_set(v___x_5467_, 0, v___x_5546_);
v___x_5556_ = v___x_5467_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5546_);
lean_ctor_set(v_reuseFailAlloc_5557_, 1, v___x_5554_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
v_a_5456_ = v___x_5556_;
goto v___jp_5455_;
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
v___jp_5455_:
{
lean_object* v___x_5457_; lean_object* v___x_5458_; 
v___x_5457_ = lean_unsigned_to_nat(1u);
v___x_5458_ = lean_nat_add(v_a_5453_, v___x_5457_);
lean_dec(v_a_5453_);
v_a_5453_ = v___x_5458_;
v_b_5454_ = v_a_5456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5579_, lean_object* v_a_5580_, lean_object* v_b_5581_){
_start:
{
lean_object* v_res_5582_; 
v_res_5582_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5579_, v_a_5580_, v_b_5581_);
lean_dec(v_upperBound_5579_);
return v_res_5582_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5583_, size_t v_i_5584_, size_t v_stop_5585_){
_start:
{
uint8_t v___x_5586_; 
v___x_5586_ = lean_usize_dec_eq(v_i_5584_, v_stop_5585_);
if (v___x_5586_ == 0)
{
uint8_t v___x_5587_; lean_object* v___x_5588_; uint8_t v___x_5589_; 
v___x_5587_ = 1;
v___x_5588_ = lean_array_uget_borrowed(v_as_5583_, v_i_5584_);
v___x_5589_ = l_Lean_Expr_isFVar(v___x_5588_);
if (v___x_5589_ == 0)
{
return v___x_5587_;
}
else
{
if (v___x_5586_ == 0)
{
size_t v___x_5590_; size_t v___x_5591_; 
v___x_5590_ = ((size_t)1ULL);
v___x_5591_ = lean_usize_add(v_i_5584_, v___x_5590_);
v_i_5584_ = v___x_5591_;
goto _start;
}
else
{
return v___x_5587_;
}
}
}
else
{
uint8_t v___x_5593_; 
v___x_5593_ = 0;
return v___x_5593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5594_, lean_object* v_i_5595_, lean_object* v_stop_5596_){
_start:
{
size_t v_i_boxed_5597_; size_t v_stop_boxed_5598_; uint8_t v_res_5599_; lean_object* v_r_5600_; 
v_i_boxed_5597_ = lean_unbox_usize(v_i_5595_);
lean_dec(v_i_5595_);
v_stop_boxed_5598_ = lean_unbox_usize(v_stop_5596_);
lean_dec(v_stop_5596_);
v_res_5599_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5594_, v_i_boxed_5597_, v_stop_boxed_5598_);
lean_dec_ref(v_as_5594_);
v_r_5600_ = lean_box(v_res_5599_);
return v_r_5600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5601_, size_t v_sz_5602_, size_t v_i_5603_, lean_object* v_bs_5604_){
_start:
{
uint8_t v___x_5605_; 
v___x_5605_ = lean_usize_dec_lt(v_i_5603_, v_sz_5602_);
if (v___x_5605_ == 0)
{
return v_bs_5604_;
}
else
{
lean_object* v_v_5606_; lean_object* v___x_5607_; lean_object* v_bs_x27_5608_; lean_object* v___y_5610_; 
v_v_5606_ = lean_array_uget(v_bs_5604_, v_i_5603_);
v___x_5607_ = lean_unsigned_to_nat(0u);
v_bs_x27_5608_ = lean_array_uset(v_bs_5604_, v_i_5603_, v___x_5607_);
if (lean_obj_tag(v_v_5606_) == 0)
{
v___y_5610_ = v_v_5606_;
goto v___jp_5609_;
}
else
{
lean_object* v_val_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; 
v_val_5615_ = lean_ctor_get(v_v_5606_, 0);
lean_inc(v_val_5615_);
lean_dec_ref(v_v_5606_);
v___x_5616_ = lean_box(0);
v___x_5617_ = lean_array_get_borrowed(v___x_5616_, v___x_5601_, v_val_5615_);
lean_dec(v_val_5615_);
lean_inc(v___x_5617_);
v___y_5610_ = v___x_5617_;
goto v___jp_5609_;
}
v___jp_5609_:
{
size_t v___x_5611_; size_t v___x_5612_; lean_object* v___x_5613_; 
v___x_5611_ = ((size_t)1ULL);
v___x_5612_ = lean_usize_add(v_i_5603_, v___x_5611_);
v___x_5613_ = lean_array_uset(v_bs_x27_5608_, v_i_5603_, v___y_5610_);
v_i_5603_ = v___x_5612_;
v_bs_5604_ = v___x_5613_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5618_, lean_object* v_sz_5619_, lean_object* v_i_5620_, lean_object* v_bs_5621_){
_start:
{
size_t v_sz_boxed_5622_; size_t v_i_boxed_5623_; lean_object* v_res_5624_; 
v_sz_boxed_5622_ = lean_unbox_usize(v_sz_5619_);
lean_dec(v_sz_5619_);
v_i_boxed_5623_ = lean_unbox_usize(v_i_5620_);
lean_dec(v_i_5620_);
v_res_5624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5618_, v_sz_boxed_5622_, v_i_boxed_5623_, v_bs_5621_);
lean_dec_ref(v___x_5618_);
return v_res_5624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5625_, size_t v_sz_5626_, size_t v_i_5627_, lean_object* v_bs_5628_){
_start:
{
uint8_t v___x_5629_; 
v___x_5629_ = lean_usize_dec_lt(v_i_5627_, v_sz_5626_);
if (v___x_5629_ == 0)
{
return v_bs_5628_;
}
else
{
lean_object* v_v_5630_; lean_object* v___x_5631_; lean_object* v_bs_x27_5632_; size_t v_sz_5633_; size_t v___x_5634_; lean_object* v___x_5635_; size_t v___x_5636_; size_t v___x_5637_; lean_object* v___x_5638_; 
v_v_5630_ = lean_array_uget(v_bs_5628_, v_i_5627_);
v___x_5631_ = lean_unsigned_to_nat(0u);
v_bs_x27_5632_ = lean_array_uset(v_bs_5628_, v_i_5627_, v___x_5631_);
v_sz_5633_ = lean_array_size(v_v_5630_);
v___x_5634_ = ((size_t)0ULL);
v___x_5635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5625_, v_sz_5633_, v___x_5634_, v_v_5630_);
v___x_5636_ = ((size_t)1ULL);
v___x_5637_ = lean_usize_add(v_i_5627_, v___x_5636_);
v___x_5638_ = lean_array_uset(v_bs_x27_5632_, v_i_5627_, v___x_5635_);
v_i_5627_ = v___x_5637_;
v_bs_5628_ = v___x_5638_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5640_, lean_object* v_sz_5641_, lean_object* v_i_5642_, lean_object* v_bs_5643_){
_start:
{
size_t v_sz_boxed_5644_; size_t v_i_boxed_5645_; lean_object* v_res_5646_; 
v_sz_boxed_5644_ = lean_unbox_usize(v_sz_5641_);
lean_dec(v_sz_5641_);
v_i_boxed_5645_ = lean_unbox_usize(v_i_5642_);
lean_dec(v_i_5642_);
v_res_5646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5640_, v_sz_boxed_5644_, v_i_boxed_5645_, v_bs_5643_);
lean_dec_ref(v___x_5640_);
return v_res_5646_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; 
v___x_5649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5650_ = lean_unsigned_to_nat(6u);
v___x_5651_ = lean_unsigned_to_nat(463u);
v___x_5652_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5653_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5654_ = l_mkPanicMessageWithDecl(v___x_5653_, v___x_5652_, v___x_5651_, v___x_5650_, v___x_5649_);
return v___x_5654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5655_, lean_object* v_as_5656_, size_t v_sz_5657_, size_t v_i_5658_, lean_object* v_b_5659_){
_start:
{
lean_object* v_a_5661_; uint8_t v___x_5665_; 
v___x_5665_ = lean_usize_dec_lt(v_i_5658_, v_sz_5657_);
if (v___x_5665_ == 0)
{
return v_b_5659_;
}
else
{
lean_object* v_a_5666_; lean_object* v___x_5667_; uint8_t v_changed_5668_; 
v_a_5666_ = lean_array_uget_borrowed(v_as_5656_, v_i_5658_);
v___x_5667_ = lean_array_get_size(v___x_5655_);
v_changed_5668_ = lean_nat_dec_lt(v_a_5666_, v___x_5667_);
if (v_changed_5668_ == 0)
{
lean_object* v___x_5669_; lean_object* v___x_5670_; 
lean_dec_ref(v_b_5659_);
v___x_5669_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5670_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5669_);
if (lean_obj_tag(v___x_5670_) == 0)
{
lean_object* v_a_5671_; 
v_a_5671_ = lean_ctor_get(v___x_5670_, 0);
lean_inc(v_a_5671_);
lean_dec_ref(v___x_5670_);
return v_a_5671_;
}
else
{
lean_object* v_a_5672_; 
v_a_5672_ = lean_ctor_get(v___x_5670_, 0);
lean_inc(v_a_5672_);
lean_dec_ref(v___x_5670_);
v_a_5661_ = v_a_5672_;
goto v___jp_5660_;
}
}
else
{
lean_object* v___x_5673_; lean_object* v___x_5674_; 
v___x_5673_ = lean_box(0);
v___x_5674_ = lean_array_get_borrowed(v___x_5673_, v___x_5655_, v_a_5666_);
if (lean_obj_tag(v___x_5674_) == 1)
{
lean_object* v_val_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; 
v_val_5675_ = lean_ctor_get(v___x_5674_, 0);
v___x_5676_ = lean_box(v_changed_5668_);
v___x_5677_ = lean_array_set(v_b_5659_, v_val_5675_, v___x_5676_);
v_a_5661_ = v___x_5677_;
goto v___jp_5660_;
}
else
{
v_a_5661_ = v_b_5659_;
goto v___jp_5660_;
}
}
}
v___jp_5660_:
{
size_t v___x_5662_; size_t v___x_5663_; 
v___x_5662_ = ((size_t)1ULL);
v___x_5663_ = lean_usize_add(v_i_5658_, v___x_5662_);
v_i_5658_ = v___x_5663_;
v_b_5659_ = v_a_5661_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5678_, lean_object* v_as_5679_, lean_object* v_sz_5680_, lean_object* v_i_5681_, lean_object* v_b_5682_){
_start:
{
size_t v_sz_boxed_5683_; size_t v_i_boxed_5684_; lean_object* v_res_5685_; 
v_sz_boxed_5683_ = lean_unbox_usize(v_sz_5680_);
lean_dec(v_sz_5680_);
v_i_boxed_5684_ = lean_unbox_usize(v_i_5681_);
lean_dec(v_i_5681_);
v_res_5685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5678_, v_as_5679_, v_sz_boxed_5683_, v_i_boxed_5684_, v_b_5682_);
lean_dec_ref(v_as_5679_);
lean_dec_ref(v___x_5678_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5686_, lean_object* v_a_5687_, lean_object* v_b_5688_){
_start:
{
uint8_t v___x_5689_; 
v___x_5689_ = lean_nat_dec_lt(v_a_5687_, v_upperBound_5686_);
if (v___x_5689_ == 0)
{
lean_dec(v_a_5687_);
return v_b_5688_;
}
else
{
lean_object* v_snd_5690_; lean_object* v_snd_5691_; lean_object* v_fst_5692_; lean_object* v___x_5694_; uint8_t v_isShared_5695_; uint8_t v_isSharedCheck_5758_; 
v_snd_5690_ = lean_ctor_get(v_b_5688_, 1);
lean_inc(v_snd_5690_);
v_snd_5691_ = lean_ctor_get(v_snd_5690_, 1);
lean_inc(v_snd_5691_);
v_fst_5692_ = lean_ctor_get(v_b_5688_, 0);
v_isSharedCheck_5758_ = !lean_is_exclusive(v_b_5688_);
if (v_isSharedCheck_5758_ == 0)
{
lean_object* v_unused_5759_; 
v_unused_5759_ = lean_ctor_get(v_b_5688_, 1);
lean_dec(v_unused_5759_);
v___x_5694_ = v_b_5688_;
v_isShared_5695_ = v_isSharedCheck_5758_;
goto v_resetjp_5693_;
}
else
{
lean_inc(v_fst_5692_);
lean_dec(v_b_5688_);
v___x_5694_ = lean_box(0);
v_isShared_5695_ = v_isSharedCheck_5758_;
goto v_resetjp_5693_;
}
v_resetjp_5693_:
{
lean_object* v_fst_5696_; lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5756_; 
v_fst_5696_ = lean_ctor_get(v_snd_5690_, 0);
v_isSharedCheck_5756_ = !lean_is_exclusive(v_snd_5690_);
if (v_isSharedCheck_5756_ == 0)
{
lean_object* v_unused_5757_; 
v_unused_5757_ = lean_ctor_get(v_snd_5690_, 1);
lean_dec(v_unused_5757_);
v___x_5698_ = v_snd_5690_;
v_isShared_5699_ = v_isSharedCheck_5756_;
goto v_resetjp_5697_;
}
else
{
lean_inc(v_fst_5696_);
lean_dec(v_snd_5690_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5756_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
lean_object* v_array_5700_; lean_object* v_start_5701_; lean_object* v_stop_5702_; uint8_t v___x_5703_; 
v_array_5700_ = lean_ctor_get(v_snd_5691_, 0);
v_start_5701_ = lean_ctor_get(v_snd_5691_, 1);
v_stop_5702_ = lean_ctor_get(v_snd_5691_, 2);
v___x_5703_ = lean_nat_dec_lt(v_start_5701_, v_stop_5702_);
if (v___x_5703_ == 0)
{
lean_object* v___x_5705_; 
lean_dec(v_a_5687_);
if (v_isShared_5699_ == 0)
{
v___x_5705_ = v___x_5698_;
goto v_reusejp_5704_;
}
else
{
lean_object* v_reuseFailAlloc_5709_; 
v_reuseFailAlloc_5709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5709_, 0, v_fst_5696_);
lean_ctor_set(v_reuseFailAlloc_5709_, 1, v_snd_5691_);
v___x_5705_ = v_reuseFailAlloc_5709_;
goto v_reusejp_5704_;
}
v_reusejp_5704_:
{
lean_object* v___x_5707_; 
if (v_isShared_5695_ == 0)
{
lean_ctor_set(v___x_5694_, 1, v___x_5705_);
v___x_5707_ = v___x_5694_;
goto v_reusejp_5706_;
}
else
{
lean_object* v_reuseFailAlloc_5708_; 
v_reuseFailAlloc_5708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5708_, 0, v_fst_5692_);
lean_ctor_set(v_reuseFailAlloc_5708_, 1, v___x_5705_);
v___x_5707_ = v_reuseFailAlloc_5708_;
goto v_reusejp_5706_;
}
v_reusejp_5706_:
{
return v___x_5707_;
}
}
}
else
{
lean_object* v___x_5711_; uint8_t v_isShared_5712_; uint8_t v_isSharedCheck_5752_; 
lean_inc(v_stop_5702_);
lean_inc(v_start_5701_);
lean_inc_ref(v_array_5700_);
v_isSharedCheck_5752_ = !lean_is_exclusive(v_snd_5691_);
if (v_isSharedCheck_5752_ == 0)
{
lean_object* v_unused_5753_; lean_object* v_unused_5754_; lean_object* v_unused_5755_; 
v_unused_5753_ = lean_ctor_get(v_snd_5691_, 2);
lean_dec(v_unused_5753_);
v_unused_5754_ = lean_ctor_get(v_snd_5691_, 1);
lean_dec(v_unused_5754_);
v_unused_5755_ = lean_ctor_get(v_snd_5691_, 0);
lean_dec(v_unused_5755_);
v___x_5711_ = v_snd_5691_;
v_isShared_5712_ = v_isSharedCheck_5752_;
goto v_resetjp_5710_;
}
else
{
lean_dec(v_snd_5691_);
v___x_5711_ = lean_box(0);
v_isShared_5712_ = v_isSharedCheck_5752_;
goto v_resetjp_5710_;
}
v_resetjp_5710_:
{
lean_object* v_array_5713_; lean_object* v_start_5714_; lean_object* v_stop_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5720_; 
v_array_5713_ = lean_ctor_get(v_fst_5696_, 0);
v_start_5714_ = lean_ctor_get(v_fst_5696_, 1);
v_stop_5715_ = lean_ctor_get(v_fst_5696_, 2);
v___x_5716_ = lean_array_fget(v_array_5700_, v_start_5701_);
v___x_5717_ = lean_unsigned_to_nat(1u);
v___x_5718_ = lean_nat_add(v_start_5701_, v___x_5717_);
lean_dec(v_start_5701_);
if (v_isShared_5712_ == 0)
{
lean_ctor_set(v___x_5711_, 1, v___x_5718_);
v___x_5720_ = v___x_5711_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_array_5700_);
lean_ctor_set(v_reuseFailAlloc_5751_, 1, v___x_5718_);
lean_ctor_set(v_reuseFailAlloc_5751_, 2, v_stop_5702_);
v___x_5720_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
uint8_t v___x_5721_; 
v___x_5721_ = lean_nat_dec_lt(v_start_5714_, v_stop_5715_);
if (v___x_5721_ == 0)
{
lean_object* v___x_5723_; 
lean_dec(v___x_5716_);
lean_dec(v_a_5687_);
if (v_isShared_5699_ == 0)
{
lean_ctor_set(v___x_5698_, 1, v___x_5720_);
v___x_5723_ = v___x_5698_;
goto v_reusejp_5722_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v_fst_5696_);
lean_ctor_set(v_reuseFailAlloc_5727_, 1, v___x_5720_);
v___x_5723_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5722_;
}
v_reusejp_5722_:
{
lean_object* v___x_5725_; 
if (v_isShared_5695_ == 0)
{
lean_ctor_set(v___x_5694_, 1, v___x_5723_);
v___x_5725_ = v___x_5694_;
goto v_reusejp_5724_;
}
else
{
lean_object* v_reuseFailAlloc_5726_; 
v_reuseFailAlloc_5726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5726_, 0, v_fst_5692_);
lean_ctor_set(v_reuseFailAlloc_5726_, 1, v___x_5723_);
v___x_5725_ = v_reuseFailAlloc_5726_;
goto v_reusejp_5724_;
}
v_reusejp_5724_:
{
return v___x_5725_;
}
}
}
else
{
lean_object* v___x_5729_; uint8_t v_isShared_5730_; uint8_t v_isSharedCheck_5747_; 
lean_inc(v_stop_5715_);
lean_inc(v_start_5714_);
lean_inc_ref(v_array_5713_);
v_isSharedCheck_5747_ = !lean_is_exclusive(v_fst_5696_);
if (v_isSharedCheck_5747_ == 0)
{
lean_object* v_unused_5748_; lean_object* v_unused_5749_; lean_object* v_unused_5750_; 
v_unused_5748_ = lean_ctor_get(v_fst_5696_, 2);
lean_dec(v_unused_5748_);
v_unused_5749_ = lean_ctor_get(v_fst_5696_, 1);
lean_dec(v_unused_5749_);
v_unused_5750_ = lean_ctor_get(v_fst_5696_, 0);
lean_dec(v_unused_5750_);
v___x_5729_ = v_fst_5696_;
v_isShared_5730_ = v_isSharedCheck_5747_;
goto v_resetjp_5728_;
}
else
{
lean_dec(v_fst_5696_);
v___x_5729_ = lean_box(0);
v_isShared_5730_ = v_isSharedCheck_5747_;
goto v_resetjp_5728_;
}
v_resetjp_5728_:
{
lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5734_; 
v___x_5731_ = lean_array_fget(v_array_5713_, v_start_5714_);
v___x_5732_ = lean_nat_add(v_start_5714_, v___x_5717_);
lean_dec(v_start_5714_);
if (v_isShared_5730_ == 0)
{
lean_ctor_set(v___x_5729_, 1, v___x_5732_);
v___x_5734_ = v___x_5729_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5746_; 
v_reuseFailAlloc_5746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5746_, 0, v_array_5713_);
lean_ctor_set(v_reuseFailAlloc_5746_, 1, v___x_5732_);
lean_ctor_set(v_reuseFailAlloc_5746_, 2, v_stop_5715_);
v___x_5734_ = v_reuseFailAlloc_5746_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
size_t v_sz_5735_; size_t v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5739_; 
v_sz_5735_ = lean_array_size(v___x_5731_);
v___x_5736_ = ((size_t)0ULL);
v___x_5737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5716_, v___x_5731_, v_sz_5735_, v___x_5736_, v_fst_5692_);
lean_dec(v___x_5731_);
lean_dec(v___x_5716_);
if (v_isShared_5699_ == 0)
{
lean_ctor_set(v___x_5698_, 1, v___x_5720_);
lean_ctor_set(v___x_5698_, 0, v___x_5734_);
v___x_5739_ = v___x_5698_;
goto v_reusejp_5738_;
}
else
{
lean_object* v_reuseFailAlloc_5745_; 
v_reuseFailAlloc_5745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5745_, 0, v___x_5734_);
lean_ctor_set(v_reuseFailAlloc_5745_, 1, v___x_5720_);
v___x_5739_ = v_reuseFailAlloc_5745_;
goto v_reusejp_5738_;
}
v_reusejp_5738_:
{
lean_object* v___x_5741_; 
if (v_isShared_5695_ == 0)
{
lean_ctor_set(v___x_5694_, 1, v___x_5739_);
lean_ctor_set(v___x_5694_, 0, v___x_5737_);
v___x_5741_ = v___x_5694_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5744_; 
v_reuseFailAlloc_5744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5744_, 0, v___x_5737_);
lean_ctor_set(v_reuseFailAlloc_5744_, 1, v___x_5739_);
v___x_5741_ = v_reuseFailAlloc_5744_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
lean_object* v___x_5742_; 
v___x_5742_ = lean_nat_add(v_a_5687_, v___x_5717_);
lean_dec(v_a_5687_);
v_a_5687_ = v___x_5742_;
v_b_5688_ = v___x_5741_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_5760_, lean_object* v_a_5761_, lean_object* v_b_5762_){
_start:
{
lean_object* v_res_5763_; 
v_res_5763_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_5760_, v_a_5761_, v_b_5762_);
lean_dec(v_upperBound_5760_);
return v_res_5763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5764_, uint8_t v___x_5765_, lean_object* v_as_5766_, size_t v_sz_5767_, size_t v_i_5768_, lean_object* v_b_5769_){
_start:
{
lean_object* v_a_5771_; uint8_t v___x_5775_; 
v___x_5775_ = lean_usize_dec_lt(v_i_5768_, v_sz_5767_);
if (v___x_5775_ == 0)
{
return v_b_5769_;
}
else
{
lean_object* v_fst_5776_; lean_object* v_snd_5777_; lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5798_; 
v_fst_5776_ = lean_ctor_get(v_b_5769_, 0);
v_snd_5777_ = lean_ctor_get(v_b_5769_, 1);
v_isSharedCheck_5798_ = !lean_is_exclusive(v_b_5769_);
if (v_isSharedCheck_5798_ == 0)
{
v___x_5779_ = v_b_5769_;
v_isShared_5780_ = v_isSharedCheck_5798_;
goto v_resetjp_5778_;
}
else
{
lean_inc(v_snd_5777_);
lean_inc(v_fst_5776_);
lean_dec(v_b_5769_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5798_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v_a_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; 
v_a_5785_ = lean_array_uget_borrowed(v_as_5766_, v_i_5768_);
v___x_5786_ = lean_box(0);
v___x_5787_ = lean_array_get_borrowed(v___x_5786_, v___x_5764_, v_a_5785_);
if (lean_obj_tag(v___x_5787_) == 1)
{
lean_object* v_val_5788_; uint8_t v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; uint8_t v___x_5792_; 
v_val_5788_ = lean_ctor_get(v___x_5787_, 0);
v___x_5789_ = 0;
v___x_5790_ = lean_box(v___x_5789_);
v___x_5791_ = lean_array_get(v___x_5790_, v_fst_5776_, v_val_5788_);
lean_dec(v___x_5790_);
v___x_5792_ = lean_unbox(v___x_5791_);
lean_dec(v___x_5791_);
if (v___x_5792_ == 0)
{
if (v___x_5765_ == 0)
{
goto v___jp_5781_;
}
else
{
lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; 
lean_del_object(v___x_5779_);
lean_dec(v_snd_5777_);
v___x_5793_ = lean_box(v___x_5765_);
v___x_5794_ = lean_array_set(v_fst_5776_, v_val_5788_, v___x_5793_);
v___x_5795_ = lean_box(v___x_5765_);
v___x_5796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5796_, 0, v___x_5794_);
lean_ctor_set(v___x_5796_, 1, v___x_5795_);
v_a_5771_ = v___x_5796_;
goto v___jp_5770_;
}
}
else
{
goto v___jp_5781_;
}
}
else
{
lean_object* v___x_5797_; 
lean_del_object(v___x_5779_);
v___x_5797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5797_, 0, v_fst_5776_);
lean_ctor_set(v___x_5797_, 1, v_snd_5777_);
v_a_5771_ = v___x_5797_;
goto v___jp_5770_;
}
v___jp_5781_:
{
lean_object* v___x_5783_; 
if (v_isShared_5780_ == 0)
{
v___x_5783_ = v___x_5779_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v_fst_5776_);
lean_ctor_set(v_reuseFailAlloc_5784_, 1, v_snd_5777_);
v___x_5783_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
v_a_5771_ = v___x_5783_;
goto v___jp_5770_;
}
}
}
}
v___jp_5770_:
{
size_t v___x_5772_; size_t v___x_5773_; 
v___x_5772_ = ((size_t)1ULL);
v___x_5773_ = lean_usize_add(v_i_5768_, v___x_5772_);
v_i_5768_ = v___x_5773_;
v_b_5769_ = v_a_5771_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5799_, lean_object* v___x_5800_, lean_object* v_as_5801_, lean_object* v_sz_5802_, lean_object* v_i_5803_, lean_object* v_b_5804_){
_start:
{
uint8_t v___x_8471__boxed_5805_; size_t v_sz_boxed_5806_; size_t v_i_boxed_5807_; lean_object* v_res_5808_; 
v___x_8471__boxed_5805_ = lean_unbox(v___x_5800_);
v_sz_boxed_5806_ = lean_unbox_usize(v_sz_5802_);
lean_dec(v_sz_5802_);
v_i_boxed_5807_ = lean_unbox_usize(v_i_5803_);
lean_dec(v_i_5803_);
v_res_5808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5799_, v___x_8471__boxed_5805_, v_as_5801_, v_sz_boxed_5806_, v_i_boxed_5807_, v_b_5804_);
lean_dec_ref(v_as_5801_);
lean_dec_ref(v___x_5799_);
return v_res_5808_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5809_, lean_object* v___x_5810_, lean_object* v_fixedParamPerms_5811_, lean_object* v_next_5812_, lean_object* v_a_5813_, lean_object* v_b_5814_){
_start:
{
lean_object* v_a_5816_; uint8_t v___x_5820_; 
v___x_5820_ = lean_nat_dec_lt(v_a_5813_, v_upperBound_5809_);
if (v___x_5820_ == 0)
{
lean_dec(v_a_5813_);
return v_b_5814_;
}
else
{
lean_object* v_fst_5821_; lean_object* v_snd_5822_; lean_object* v___x_5824_; uint8_t v_isShared_5825_; uint8_t v_isSharedCheck_5858_; 
v_fst_5821_ = lean_ctor_get(v_b_5814_, 0);
v_snd_5822_ = lean_ctor_get(v_b_5814_, 1);
v_isSharedCheck_5858_ = !lean_is_exclusive(v_b_5814_);
if (v_isSharedCheck_5858_ == 0)
{
v___x_5824_ = v_b_5814_;
v_isShared_5825_ = v_isSharedCheck_5858_;
goto v_resetjp_5823_;
}
else
{
lean_inc(v_snd_5822_);
lean_inc(v_fst_5821_);
lean_dec(v_b_5814_);
v___x_5824_ = lean_box(0);
v_isShared_5825_ = v_isSharedCheck_5858_;
goto v_resetjp_5823_;
}
v_resetjp_5823_:
{
lean_object* v___x_5826_; 
v___x_5826_ = lean_array_fget_borrowed(v___x_5810_, v_a_5813_);
if (lean_obj_tag(v___x_5826_) == 1)
{
lean_object* v_val_5827_; uint8_t v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; uint8_t v___x_5831_; 
v_val_5827_ = lean_ctor_get(v___x_5826_, 0);
v___x_5828_ = 0;
v___x_5829_ = lean_box(v___x_5828_);
v___x_5830_ = lean_array_get(v___x_5829_, v_fst_5821_, v_val_5827_);
lean_dec(v___x_5829_);
v___x_5831_ = lean_unbox(v___x_5830_);
if (v___x_5831_ == 0)
{
lean_object* v___x_5833_; 
lean_dec(v___x_5830_);
if (v_isShared_5825_ == 0)
{
v___x_5833_ = v___x_5824_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5834_; 
v_reuseFailAlloc_5834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5834_, 0, v_fst_5821_);
lean_ctor_set(v_reuseFailAlloc_5834_, 1, v_snd_5822_);
v___x_5833_ = v_reuseFailAlloc_5834_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
v_a_5816_ = v___x_5833_;
goto v___jp_5815_;
}
}
else
{
lean_object* v_revDeps_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5840_; 
v_revDeps_5835_ = lean_ctor_get(v_fixedParamPerms_5811_, 2);
v___x_5836_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_5837_ = lean_array_get_borrowed(v___x_5836_, v_revDeps_5835_, v_next_5812_);
v___x_5838_ = lean_array_get_borrowed(v___x_5836_, v___x_5837_, v_a_5813_);
if (v_isShared_5825_ == 0)
{
v___x_5840_ = v___x_5824_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5854_; 
v_reuseFailAlloc_5854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_fst_5821_);
lean_ctor_set(v_reuseFailAlloc_5854_, 1, v_snd_5822_);
v___x_5840_ = v_reuseFailAlloc_5854_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
size_t v_sz_5841_; size_t v___x_5842_; uint8_t v___x_5843_; lean_object* v___x_5844_; lean_object* v_fst_5845_; lean_object* v_snd_5846_; lean_object* v___x_5848_; uint8_t v_isShared_5849_; uint8_t v_isSharedCheck_5853_; 
v_sz_5841_ = lean_array_size(v___x_5838_);
v___x_5842_ = ((size_t)0ULL);
v___x_5843_ = lean_unbox(v___x_5830_);
lean_dec(v___x_5830_);
v___x_5844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5810_, v___x_5843_, v___x_5838_, v_sz_5841_, v___x_5842_, v___x_5840_);
v_fst_5845_ = lean_ctor_get(v___x_5844_, 0);
v_snd_5846_ = lean_ctor_get(v___x_5844_, 1);
v_isSharedCheck_5853_ = !lean_is_exclusive(v___x_5844_);
if (v_isSharedCheck_5853_ == 0)
{
v___x_5848_ = v___x_5844_;
v_isShared_5849_ = v_isSharedCheck_5853_;
goto v_resetjp_5847_;
}
else
{
lean_inc(v_snd_5846_);
lean_inc(v_fst_5845_);
lean_dec(v___x_5844_);
v___x_5848_ = lean_box(0);
v_isShared_5849_ = v_isSharedCheck_5853_;
goto v_resetjp_5847_;
}
v_resetjp_5847_:
{
lean_object* v___x_5851_; 
if (v_isShared_5849_ == 0)
{
v___x_5851_ = v___x_5848_;
goto v_reusejp_5850_;
}
else
{
lean_object* v_reuseFailAlloc_5852_; 
v_reuseFailAlloc_5852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5852_, 0, v_fst_5845_);
lean_ctor_set(v_reuseFailAlloc_5852_, 1, v_snd_5846_);
v___x_5851_ = v_reuseFailAlloc_5852_;
goto v_reusejp_5850_;
}
v_reusejp_5850_:
{
v_a_5816_ = v___x_5851_;
goto v___jp_5815_;
}
}
}
}
}
else
{
lean_object* v___x_5856_; 
if (v_isShared_5825_ == 0)
{
v___x_5856_ = v___x_5824_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v_fst_5821_);
lean_ctor_set(v_reuseFailAlloc_5857_, 1, v_snd_5822_);
v___x_5856_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
v_a_5816_ = v___x_5856_;
goto v___jp_5815_;
}
}
}
}
v___jp_5815_:
{
lean_object* v___x_5817_; lean_object* v___x_5818_; 
v___x_5817_ = lean_unsigned_to_nat(1u);
v___x_5818_ = lean_nat_add(v_a_5813_, v___x_5817_);
lean_dec(v_a_5813_);
v_a_5813_ = v___x_5818_;
v_b_5814_ = v_a_5816_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5859_, lean_object* v___x_5860_, lean_object* v_fixedParamPerms_5861_, lean_object* v_next_5862_, lean_object* v_a_5863_, lean_object* v_b_5864_){
_start:
{
lean_object* v_res_5865_; 
v_res_5865_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5859_, v___x_5860_, v_fixedParamPerms_5861_, v_next_5862_, v_a_5863_, v_b_5864_);
lean_dec(v_next_5862_);
lean_dec_ref(v_fixedParamPerms_5861_);
lean_dec_ref(v___x_5860_);
lean_dec(v_upperBound_5859_);
return v_res_5865_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5866_, lean_object* v___x_5867_, lean_object* v_fixedParamPerms_5868_, lean_object* v_a_5869_, lean_object* v_b_5870_){
_start:
{
uint8_t v___x_5871_; 
v___x_5871_ = lean_nat_dec_lt(v_a_5869_, v_upperBound_5866_);
if (v___x_5871_ == 0)
{
lean_dec(v_a_5869_);
return v_b_5870_;
}
else
{
lean_object* v_fst_5872_; lean_object* v_snd_5873_; lean_object* v___x_5875_; uint8_t v_isShared_5876_; uint8_t v_isSharedCheck_5896_; 
v_fst_5872_ = lean_ctor_get(v_b_5870_, 0);
v_snd_5873_ = lean_ctor_get(v_b_5870_, 1);
v_isSharedCheck_5896_ = !lean_is_exclusive(v_b_5870_);
if (v_isSharedCheck_5896_ == 0)
{
v___x_5875_ = v_b_5870_;
v_isShared_5876_ = v_isSharedCheck_5896_;
goto v_resetjp_5874_;
}
else
{
lean_inc(v_snd_5873_);
lean_inc(v_fst_5872_);
lean_dec(v_b_5870_);
v___x_5875_ = lean_box(0);
v_isShared_5876_ = v_isSharedCheck_5896_;
goto v_resetjp_5874_;
}
v_resetjp_5874_:
{
lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5881_; 
v___x_5877_ = lean_array_fget_borrowed(v___x_5867_, v_a_5869_);
v___x_5878_ = lean_array_get_size(v___x_5877_);
v___x_5879_ = lean_unsigned_to_nat(0u);
if (v_isShared_5876_ == 0)
{
v___x_5881_ = v___x_5875_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_fst_5872_);
lean_ctor_set(v_reuseFailAlloc_5895_, 1, v_snd_5873_);
v___x_5881_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
lean_object* v___x_5882_; lean_object* v_fst_5883_; lean_object* v_snd_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5894_; 
v___x_5882_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5878_, v___x_5877_, v_fixedParamPerms_5868_, v_a_5869_, v___x_5879_, v___x_5881_);
v_fst_5883_ = lean_ctor_get(v___x_5882_, 0);
v_snd_5884_ = lean_ctor_get(v___x_5882_, 1);
v_isSharedCheck_5894_ = !lean_is_exclusive(v___x_5882_);
if (v_isSharedCheck_5894_ == 0)
{
v___x_5886_ = v___x_5882_;
v_isShared_5887_ = v_isSharedCheck_5894_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_snd_5884_);
lean_inc(v_fst_5883_);
lean_dec(v___x_5882_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_5894_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
lean_object* v___x_5889_; 
if (v_isShared_5887_ == 0)
{
v___x_5889_ = v___x_5886_;
goto v_reusejp_5888_;
}
else
{
lean_object* v_reuseFailAlloc_5893_; 
v_reuseFailAlloc_5893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5893_, 0, v_fst_5883_);
lean_ctor_set(v_reuseFailAlloc_5893_, 1, v_snd_5884_);
v___x_5889_ = v_reuseFailAlloc_5893_;
goto v_reusejp_5888_;
}
v_reusejp_5888_:
{
lean_object* v___x_5890_; lean_object* v___x_5891_; 
v___x_5890_ = lean_unsigned_to_nat(1u);
v___x_5891_ = lean_nat_add(v_a_5869_, v___x_5890_);
lean_dec(v_a_5869_);
v_a_5869_ = v___x_5891_;
v_b_5870_ = v___x_5889_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5897_, lean_object* v___x_5898_, lean_object* v_fixedParamPerms_5899_, lean_object* v_a_5900_, lean_object* v_b_5901_){
_start:
{
lean_object* v_res_5902_; 
v_res_5902_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5897_, v___x_5898_, v_fixedParamPerms_5899_, v_a_5900_, v_b_5901_);
lean_dec_ref(v_fixedParamPerms_5899_);
lean_dec_ref(v___x_5898_);
lean_dec(v_upperBound_5897_);
return v_res_5902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_5903_, lean_object* v___x_5904_, lean_object* v_fixedParamPerms_5905_, lean_object* v_b_5906_){
_start:
{
lean_object* v_snd_5907_; uint8_t v___x_5908_; 
v_snd_5907_ = lean_ctor_get(v_b_5906_, 1);
v___x_5908_ = lean_unbox(v_snd_5907_);
if (v___x_5908_ == 0)
{
lean_object* v_fst_5909_; lean_object* v___x_5911_; uint8_t v_isShared_5912_; uint8_t v_isSharedCheck_5916_; 
lean_inc(v_snd_5907_);
v_fst_5909_ = lean_ctor_get(v_b_5906_, 0);
v_isSharedCheck_5916_ = !lean_is_exclusive(v_b_5906_);
if (v_isSharedCheck_5916_ == 0)
{
lean_object* v_unused_5917_; 
v_unused_5917_ = lean_ctor_get(v_b_5906_, 1);
lean_dec(v_unused_5917_);
v___x_5911_ = v_b_5906_;
v_isShared_5912_ = v_isSharedCheck_5916_;
goto v_resetjp_5910_;
}
else
{
lean_inc(v_fst_5909_);
lean_dec(v_b_5906_);
v___x_5911_ = lean_box(0);
v_isShared_5912_ = v_isSharedCheck_5916_;
goto v_resetjp_5910_;
}
v_resetjp_5910_:
{
lean_object* v___x_5914_; 
if (v_isShared_5912_ == 0)
{
v___x_5914_ = v___x_5911_;
goto v_reusejp_5913_;
}
else
{
lean_object* v_reuseFailAlloc_5915_; 
v_reuseFailAlloc_5915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5915_, 0, v_fst_5909_);
lean_ctor_set(v_reuseFailAlloc_5915_, 1, v_snd_5907_);
v___x_5914_ = v_reuseFailAlloc_5915_;
goto v_reusejp_5913_;
}
v_reusejp_5913_:
{
return v___x_5914_;
}
}
}
else
{
lean_object* v_fst_5918_; lean_object* v___x_5920_; uint8_t v_isShared_5921_; uint8_t v_isSharedCheck_5939_; 
v_fst_5918_ = lean_ctor_get(v_b_5906_, 0);
v_isSharedCheck_5939_ = !lean_is_exclusive(v_b_5906_);
if (v_isSharedCheck_5939_ == 0)
{
lean_object* v_unused_5940_; 
v_unused_5940_ = lean_ctor_get(v_b_5906_, 1);
lean_dec(v_unused_5940_);
v___x_5920_ = v_b_5906_;
v_isShared_5921_ = v_isSharedCheck_5939_;
goto v_resetjp_5919_;
}
else
{
lean_inc(v_fst_5918_);
lean_dec(v_b_5906_);
v___x_5920_ = lean_box(0);
v_isShared_5921_ = v_isSharedCheck_5939_;
goto v_resetjp_5919_;
}
v_resetjp_5919_:
{
uint8_t v_changed_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5926_; 
v_changed_5922_ = 0;
v___x_5923_ = lean_unsigned_to_nat(0u);
v___x_5924_ = lean_box(v_changed_5922_);
if (v_isShared_5921_ == 0)
{
lean_ctor_set(v___x_5920_, 1, v___x_5924_);
v___x_5926_ = v___x_5920_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_5938_; 
v_reuseFailAlloc_5938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5938_, 0, v_fst_5918_);
lean_ctor_set(v_reuseFailAlloc_5938_, 1, v___x_5924_);
v___x_5926_ = v_reuseFailAlloc_5938_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
lean_object* v___x_5927_; lean_object* v_fst_5928_; lean_object* v_snd_5929_; lean_object* v___x_5931_; uint8_t v_isShared_5932_; uint8_t v_isSharedCheck_5937_; 
v___x_5927_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5903_, v___x_5904_, v_fixedParamPerms_5905_, v___x_5923_, v___x_5926_);
v_fst_5928_ = lean_ctor_get(v___x_5927_, 0);
v_snd_5929_ = lean_ctor_get(v___x_5927_, 1);
v_isSharedCheck_5937_ = !lean_is_exclusive(v___x_5927_);
if (v_isSharedCheck_5937_ == 0)
{
v___x_5931_ = v___x_5927_;
v_isShared_5932_ = v_isSharedCheck_5937_;
goto v_resetjp_5930_;
}
else
{
lean_inc(v_snd_5929_);
lean_inc(v_fst_5928_);
lean_dec(v___x_5927_);
v___x_5931_ = lean_box(0);
v_isShared_5932_ = v_isSharedCheck_5937_;
goto v_resetjp_5930_;
}
v_resetjp_5930_:
{
lean_object* v___x_5934_; 
if (v_isShared_5932_ == 0)
{
v___x_5934_ = v___x_5931_;
goto v_reusejp_5933_;
}
else
{
lean_object* v_reuseFailAlloc_5936_; 
v_reuseFailAlloc_5936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5936_, 0, v_fst_5928_);
lean_ctor_set(v_reuseFailAlloc_5936_, 1, v_snd_5929_);
v___x_5934_ = v_reuseFailAlloc_5936_;
goto v_reusejp_5933_;
}
v_reusejp_5933_:
{
v_b_5906_ = v___x_5934_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_5941_, lean_object* v___x_5942_, lean_object* v_fixedParamPerms_5943_, lean_object* v_b_5944_){
_start:
{
lean_object* v_res_5945_; 
v_res_5945_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_5941_, v___x_5942_, v_fixedParamPerms_5943_, v_b_5944_);
lean_dec_ref(v_fixedParamPerms_5943_);
lean_dec_ref(v___x_5942_);
lean_dec(v___x_5941_);
return v_res_5945_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; 
v___x_5947_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_5948_ = lean_unsigned_to_nat(2u);
v___x_5949_ = lean_unsigned_to_nat(457u);
v___x_5950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5951_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5952_ = l_mkPanicMessageWithDecl(v___x_5951_, v___x_5950_, v___x_5949_, v___x_5948_, v___x_5947_);
return v___x_5952_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; 
v___x_5954_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_5955_ = lean_unsigned_to_nat(2u);
v___x_5956_ = lean_unsigned_to_nat(458u);
v___x_5957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5958_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5959_ = l_mkPanicMessageWithDecl(v___x_5958_, v___x_5957_, v___x_5956_, v___x_5955_, v___x_5954_);
return v___x_5959_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; 
v___x_5961_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_5962_ = lean_unsigned_to_nat(2u);
v___x_5963_ = lean_unsigned_to_nat(456u);
v___x_5964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5965_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__8___redArg___lam__2___closed__0));
v___x_5966_ = l_mkPanicMessageWithDecl(v___x_5965_, v___x_5964_, v___x_5963_, v___x_5962_, v___x_5961_);
return v___x_5966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_5967_, lean_object* v_xs_5968_, lean_object* v_toErase_5969_){
_start:
{
lean_object* v___x_5970_; lean_object* v___x_5971_; uint8_t v___x_6055_; 
v___x_5970_ = lean_unsigned_to_nat(0u);
v___x_5971_ = lean_array_get_size(v_xs_5968_);
v___x_6055_ = lean_nat_dec_lt(v___x_5970_, v___x_5971_);
if (v___x_6055_ == 0)
{
goto v___jp_5972_;
}
else
{
if (v___x_6055_ == 0)
{
goto v___jp_5972_;
}
else
{
size_t v___x_6056_; size_t v___x_6057_; uint8_t v___x_6058_; 
v___x_6056_ = ((size_t)0ULL);
v___x_6057_ = lean_usize_of_nat(v___x_5971_);
v___x_6058_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_5968_, v___x_6056_, v___x_6057_);
if (v___x_6058_ == 0)
{
goto v___jp_5972_;
}
else
{
lean_object* v___x_6059_; lean_object* v___x_6060_; 
lean_dec_ref(v_toErase_5969_);
lean_dec_ref(v_xs_5968_);
lean_dec_ref(v_fixedParamPerms_5967_);
v___x_6059_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6060_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6059_);
return v___x_6060_;
}
}
}
v___jp_5972_:
{
lean_object* v_numFixed_5973_; lean_object* v_perms_5974_; lean_object* v_revDeps_5975_; uint8_t v___x_5976_; 
v_numFixed_5973_ = lean_ctor_get(v_fixedParamPerms_5967_, 0);
v_perms_5974_ = lean_ctor_get(v_fixedParamPerms_5967_, 1);
lean_inc_ref(v_perms_5974_);
v_revDeps_5975_ = lean_ctor_get(v_fixedParamPerms_5967_, 2);
lean_inc_ref(v_revDeps_5975_);
v___x_5976_ = lean_nat_dec_eq(v_numFixed_5973_, v___x_5971_);
if (v___x_5976_ == 0)
{
lean_object* v___x_5977_; lean_object* v___x_5978_; 
lean_dec_ref(v_revDeps_5975_);
lean_dec_ref(v_perms_5974_);
lean_dec_ref(v_toErase_5969_);
lean_dec_ref(v_xs_5968_);
lean_dec_ref(v_fixedParamPerms_5967_);
v___x_5977_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_5978_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_5977_);
return v___x_5978_;
}
else
{
lean_object* v___x_5979_; lean_object* v___x_5980_; uint8_t v_changed_5981_; 
v___x_5979_ = lean_array_get_size(v_toErase_5969_);
v___x_5980_ = lean_array_get_size(v_perms_5974_);
v_changed_5981_ = lean_nat_dec_eq(v___x_5979_, v___x_5980_);
if (v_changed_5981_ == 0)
{
lean_object* v___x_5982_; lean_object* v___x_5983_; 
lean_dec_ref(v_revDeps_5975_);
lean_dec_ref(v_perms_5974_);
lean_dec_ref(v_toErase_5969_);
lean_dec_ref(v_xs_5968_);
lean_dec_ref(v_fixedParamPerms_5967_);
v___x_5982_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_5983_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_5982_);
return v___x_5983_;
}
else
{
uint8_t v_changed_5984_; lean_object* v___x_5985_; lean_object* v_mask_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v_fst_5992_; lean_object* v___x_5994_; uint8_t v_isShared_5995_; uint8_t v_isSharedCheck_6053_; 
v_changed_5984_ = 0;
v___x_5985_ = lean_box(v_changed_5984_);
lean_inc(v_numFixed_5973_);
v_mask_5986_ = lean_mk_array(v_numFixed_5973_, v___x_5985_);
v___x_5987_ = l_Array_toSubarray___redArg(v_toErase_5969_, v___x_5970_, v___x_5979_);
lean_inc_ref(v_perms_5974_);
v___x_5988_ = l_Array_toSubarray___redArg(v_perms_5974_, v___x_5970_, v___x_5980_);
v___x_5989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5989_, 0, v___x_5987_);
lean_ctor_set(v___x_5989_, 1, v___x_5988_);
v___x_5990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5990_, 0, v_mask_5986_);
lean_ctor_set(v___x_5990_, 1, v___x_5989_);
v___x_5991_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_5979_, v___x_5970_, v___x_5990_);
v_fst_5992_ = lean_ctor_get(v___x_5991_, 0);
v_isSharedCheck_6053_ = !lean_is_exclusive(v___x_5991_);
if (v_isSharedCheck_6053_ == 0)
{
lean_object* v_unused_6054_; 
v_unused_6054_ = lean_ctor_get(v___x_5991_, 1);
lean_dec(v_unused_6054_);
v___x_5994_ = v___x_5991_;
v_isShared_5995_ = v_isSharedCheck_6053_;
goto v_resetjp_5993_;
}
else
{
lean_inc(v_fst_5992_);
lean_dec(v___x_5991_);
v___x_5994_ = lean_box(0);
v_isShared_5995_ = v_isSharedCheck_6053_;
goto v_resetjp_5993_;
}
v_resetjp_5993_:
{
lean_object* v___x_5996_; lean_object* v___x_5998_; 
v___x_5996_ = lean_box(v_changed_5981_);
if (v_isShared_5995_ == 0)
{
lean_ctor_set(v___x_5994_, 1, v___x_5996_);
v___x_5998_ = v___x_5994_;
goto v_reusejp_5997_;
}
else
{
lean_object* v_reuseFailAlloc_6052_; 
v_reuseFailAlloc_6052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6052_, 0, v_fst_5992_);
lean_ctor_set(v_reuseFailAlloc_6052_, 1, v___x_5996_);
v___x_5998_ = v_reuseFailAlloc_6052_;
goto v_reusejp_5997_;
}
v_reusejp_5997_:
{
lean_object* v___x_5999_; lean_object* v___x_6001_; uint8_t v_isShared_6002_; uint8_t v_isSharedCheck_6048_; 
v___x_5999_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_5980_, v_perms_5974_, v_fixedParamPerms_5967_, v___x_5998_);
v_isSharedCheck_6048_ = !lean_is_exclusive(v_fixedParamPerms_5967_);
if (v_isSharedCheck_6048_ == 0)
{
lean_object* v_unused_6049_; lean_object* v_unused_6050_; lean_object* v_unused_6051_; 
v_unused_6049_ = lean_ctor_get(v_fixedParamPerms_5967_, 2);
lean_dec(v_unused_6049_);
v_unused_6050_ = lean_ctor_get(v_fixedParamPerms_5967_, 1);
lean_dec(v_unused_6050_);
v_unused_6051_ = lean_ctor_get(v_fixedParamPerms_5967_, 0);
lean_dec(v_unused_6051_);
v___x_6001_ = v_fixedParamPerms_5967_;
v_isShared_6002_ = v_isSharedCheck_6048_;
goto v_resetjp_6000_;
}
else
{
lean_dec(v_fixedParamPerms_5967_);
v___x_6001_ = lean_box(0);
v_isShared_6002_ = v_isSharedCheck_6048_;
goto v_resetjp_6000_;
}
v_resetjp_6000_:
{
lean_object* v_fst_6003_; lean_object* v___x_6005_; uint8_t v_isShared_6006_; uint8_t v_isSharedCheck_6046_; 
v_fst_6003_ = lean_ctor_get(v___x_5999_, 0);
v_isSharedCheck_6046_ = !lean_is_exclusive(v___x_5999_);
if (v_isSharedCheck_6046_ == 0)
{
lean_object* v_unused_6047_; 
v_unused_6047_ = lean_ctor_get(v___x_5999_, 1);
lean_dec(v_unused_6047_);
v___x_6005_ = v___x_5999_;
v_isShared_6006_ = v_isSharedCheck_6046_;
goto v_resetjp_6004_;
}
else
{
lean_inc(v_fst_6003_);
lean_dec(v___x_5999_);
v___x_6005_ = lean_box(0);
v_isShared_6006_ = v_isSharedCheck_6046_;
goto v_resetjp_6004_;
}
v_resetjp_6004_:
{
lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6012_; 
v___x_6007_ = lean_array_get_size(v_fst_6003_);
v___x_6008_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6009_ = l_Array_toSubarray___redArg(v_fst_6003_, v___x_5970_, v___x_6007_);
v___x_6010_ = l_Array_toSubarray___redArg(v_xs_5968_, v___x_5970_, v___x_5971_);
if (v_isShared_6006_ == 0)
{
lean_ctor_set(v___x_6005_, 1, v___x_6010_);
lean_ctor_set(v___x_6005_, 0, v___x_6009_);
v___x_6012_ = v___x_6005_;
goto v_reusejp_6011_;
}
else
{
lean_object* v_reuseFailAlloc_6045_; 
v_reuseFailAlloc_6045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6045_, 0, v___x_6009_);
lean_ctor_set(v_reuseFailAlloc_6045_, 1, v___x_6010_);
v___x_6012_ = v_reuseFailAlloc_6045_;
goto v_reusejp_6011_;
}
v_reusejp_6011_:
{
lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v_snd_6017_; lean_object* v_snd_6018_; lean_object* v_fst_6019_; lean_object* v_fst_6020_; lean_object* v___x_6022_; uint8_t v_isShared_6023_; uint8_t v_isSharedCheck_6043_; 
v___x_6013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6008_);
lean_ctor_set(v___x_6013_, 1, v___x_6012_);
v___x_6014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6008_);
lean_ctor_set(v___x_6014_, 1, v___x_6013_);
v___x_6015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6008_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
v___x_6016_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6007_, v___x_5970_, v___x_6015_);
v_snd_6017_ = lean_ctor_get(v___x_6016_, 1);
lean_inc(v_snd_6017_);
v_snd_6018_ = lean_ctor_get(v_snd_6017_, 1);
lean_inc(v_snd_6018_);
v_fst_6019_ = lean_ctor_get(v___x_6016_, 0);
lean_inc(v_fst_6019_);
lean_dec_ref(v___x_6016_);
v_fst_6020_ = lean_ctor_get(v_snd_6017_, 0);
v_isSharedCheck_6043_ = !lean_is_exclusive(v_snd_6017_);
if (v_isSharedCheck_6043_ == 0)
{
lean_object* v_unused_6044_; 
v_unused_6044_ = lean_ctor_get(v_snd_6017_, 1);
lean_dec(v_unused_6044_);
v___x_6022_ = v_snd_6017_;
v_isShared_6023_ = v_isSharedCheck_6043_;
goto v_resetjp_6021_;
}
else
{
lean_inc(v_fst_6020_);
lean_dec(v_snd_6017_);
v___x_6022_ = lean_box(0);
v_isShared_6023_ = v_isSharedCheck_6043_;
goto v_resetjp_6021_;
}
v_resetjp_6021_:
{
lean_object* v_fst_6024_; lean_object* v___x_6026_; uint8_t v_isShared_6027_; uint8_t v_isSharedCheck_6041_; 
v_fst_6024_ = lean_ctor_get(v_snd_6018_, 0);
v_isSharedCheck_6041_ = !lean_is_exclusive(v_snd_6018_);
if (v_isSharedCheck_6041_ == 0)
{
lean_object* v_unused_6042_; 
v_unused_6042_ = lean_ctor_get(v_snd_6018_, 1);
lean_dec(v_unused_6042_);
v___x_6026_ = v_snd_6018_;
v_isShared_6027_ = v_isSharedCheck_6041_;
goto v_resetjp_6025_;
}
else
{
lean_inc(v_fst_6024_);
lean_dec(v_snd_6018_);
v___x_6026_ = lean_box(0);
v_isShared_6027_ = v_isSharedCheck_6041_;
goto v_resetjp_6025_;
}
v_resetjp_6025_:
{
lean_object* v___x_6028_; size_t v_sz_6029_; size_t v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6033_; 
v___x_6028_ = lean_array_get_size(v_fst_6024_);
v_sz_6029_ = lean_array_size(v_perms_5974_);
v___x_6030_ = ((size_t)0ULL);
v___x_6031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6019_, v_sz_6029_, v___x_6030_, v_perms_5974_);
lean_dec(v_fst_6019_);
if (v_isShared_6002_ == 0)
{
lean_ctor_set(v___x_6001_, 1, v___x_6031_);
lean_ctor_set(v___x_6001_, 0, v___x_6028_);
v___x_6033_ = v___x_6001_;
goto v_reusejp_6032_;
}
else
{
lean_object* v_reuseFailAlloc_6040_; 
v_reuseFailAlloc_6040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6040_, 0, v___x_6028_);
lean_ctor_set(v_reuseFailAlloc_6040_, 1, v___x_6031_);
lean_ctor_set(v_reuseFailAlloc_6040_, 2, v_revDeps_5975_);
v___x_6033_ = v_reuseFailAlloc_6040_;
goto v_reusejp_6032_;
}
v_reusejp_6032_:
{
lean_object* v___x_6035_; 
if (v_isShared_6027_ == 0)
{
lean_ctor_set(v___x_6026_, 1, v_fst_6020_);
v___x_6035_ = v___x_6026_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6039_; 
v_reuseFailAlloc_6039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6039_, 0, v_fst_6024_);
lean_ctor_set(v_reuseFailAlloc_6039_, 1, v_fst_6020_);
v___x_6035_ = v_reuseFailAlloc_6039_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
lean_object* v___x_6037_; 
if (v_isShared_6023_ == 0)
{
lean_ctor_set(v___x_6022_, 1, v___x_6035_);
lean_ctor_set(v___x_6022_, 0, v___x_6033_);
v___x_6037_ = v___x_6022_;
goto v_reusejp_6036_;
}
else
{
lean_object* v_reuseFailAlloc_6038_; 
v_reuseFailAlloc_6038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6038_, 0, v___x_6033_);
lean_ctor_set(v_reuseFailAlloc_6038_, 1, v___x_6035_);
v___x_6037_ = v_reuseFailAlloc_6038_;
goto v_reusejp_6036_;
}
v_reusejp_6036_:
{
return v___x_6037_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6061_, lean_object* v___x_6062_, lean_object* v_fixedParamPerms_6063_, lean_object* v_next_6064_, lean_object* v_inst_6065_, lean_object* v_R_6066_, lean_object* v_a_6067_, lean_object* v_b_6068_, lean_object* v_c_6069_){
_start:
{
lean_object* v___x_6070_; 
v___x_6070_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6061_, v___x_6062_, v_fixedParamPerms_6063_, v_next_6064_, v_a_6067_, v_b_6068_);
return v___x_6070_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6071_, lean_object* v___x_6072_, lean_object* v_fixedParamPerms_6073_, lean_object* v_next_6074_, lean_object* v_inst_6075_, lean_object* v_R_6076_, lean_object* v_a_6077_, lean_object* v_b_6078_, lean_object* v_c_6079_){
_start:
{
lean_object* v_res_6080_; 
v_res_6080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6071_, v___x_6072_, v_fixedParamPerms_6073_, v_next_6074_, v_inst_6075_, v_R_6076_, v_a_6077_, v_b_6078_, v_c_6079_);
lean_dec(v_next_6074_);
lean_dec_ref(v_fixedParamPerms_6073_);
lean_dec_ref(v___x_6072_);
lean_dec(v_upperBound_6071_);
return v_res_6080_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6081_, lean_object* v___x_6082_, lean_object* v_fixedParamPerms_6083_, lean_object* v_inst_6084_, lean_object* v_R_6085_, lean_object* v_a_6086_, lean_object* v_b_6087_, lean_object* v_c_6088_){
_start:
{
lean_object* v___x_6089_; 
v___x_6089_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6081_, v___x_6082_, v_fixedParamPerms_6083_, v_a_6086_, v_b_6087_);
return v___x_6089_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6090_, lean_object* v___x_6091_, lean_object* v_fixedParamPerms_6092_, lean_object* v_inst_6093_, lean_object* v_R_6094_, lean_object* v_a_6095_, lean_object* v_b_6096_, lean_object* v_c_6097_){
_start:
{
lean_object* v_res_6098_; 
v_res_6098_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6090_, v___x_6091_, v_fixedParamPerms_6092_, v_inst_6093_, v_R_6094_, v_a_6095_, v_b_6096_, v_c_6097_);
lean_dec_ref(v_fixedParamPerms_6092_);
lean_dec_ref(v___x_6091_);
lean_dec(v_upperBound_6090_);
return v_res_6098_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6099_, lean_object* v_inst_6100_, lean_object* v_R_6101_, lean_object* v_a_6102_, lean_object* v_b_6103_, lean_object* v_c_6104_){
_start:
{
lean_object* v___x_6105_; 
v___x_6105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6099_, v_a_6102_, v_b_6103_);
return v___x_6105_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6106_, lean_object* v_inst_6107_, lean_object* v_R_6108_, lean_object* v_a_6109_, lean_object* v_b_6110_, lean_object* v_c_6111_){
_start:
{
lean_object* v_res_6112_; 
v_res_6112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6106_, v_inst_6107_, v_R_6108_, v_a_6109_, v_b_6110_, v_c_6111_);
lean_dec(v_upperBound_6106_);
return v_res_6112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6113_, lean_object* v_inst_6114_, lean_object* v_R_6115_, lean_object* v_a_6116_, lean_object* v_b_6117_, lean_object* v_c_6118_){
_start:
{
lean_object* v___x_6119_; 
v___x_6119_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6113_, v_a_6116_, v_b_6117_);
return v___x_6119_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6120_, lean_object* v_inst_6121_, lean_object* v_R_6122_, lean_object* v_a_6123_, lean_object* v_b_6124_, lean_object* v_c_6125_){
_start:
{
lean_object* v_res_6126_; 
v_res_6126_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6120_, v_inst_6121_, v_R_6122_, v_a_6123_, v_b_6124_, v_c_6125_);
lean_dec(v_upperBound_6120_);
return v_res_6126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6184_; uint8_t v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; 
v___x_6184_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__3));
v___x_6185_ = 0;
v___x_6186_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6187_ = l_Lean_registerTraceClass(v___x_6184_, v___x_6185_, v___x_6186_);
return v___x_6187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6188_){
_start:
{
lean_object* v_res_6189_; 
v_res_6189_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6189_;
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
