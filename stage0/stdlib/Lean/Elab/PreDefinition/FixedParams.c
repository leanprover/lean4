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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "getFixedParams: notFixed "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ":\nIn "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "\ntoo few arguments for "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =/= "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " not matched"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__0_value;
static lean_once_cell_t l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedFixedParamPerms_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedFixedParamPerms;
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
lean_inc_ref(v_mctx_706_);
lean_dec(v___x_680_);
v___f_707_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__0));
v___f_708_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_708_, 0, v_fvarId_677_);
v___x_709_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
lean_inc_ref(v_mctx_706_);
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
v___x_744_ = lean_apply_7(v_k_736_, v_b_737_, v_c_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, lean_box(0));
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed(lean_object* v_k_745_, lean_object* v_b_746_, lean_object* v_c_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0(v_k_745_, v_b_746_, v_c_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
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
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
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
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
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
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
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
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
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
lean_inc(v___y_877_);
lean_inc_ref(v___y_876_);
lean_inc(v___y_875_);
lean_inc_ref(v___y_874_);
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
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
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
lean_dec_ref(v_xs_989_);
lean_dec(v___x_988_);
lean_dec(v_upperBound_987_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg(lean_object* v_cls_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_options_1007_; uint8_t v_hasTrace_1008_; 
v_options_1007_ = lean_ctor_get(v___y_1005_, 2);
v_hasTrace_1008_ = lean_ctor_get_uint8(v_options_1007_, sizeof(void*)*1);
if (v_hasTrace_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_dec(v_cls_1004_);
v___x_1009_ = lean_box(v_hasTrace_1008_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
else
{
lean_object* v_inheritedTraceOptions_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_inheritedTraceOptions_1011_ = lean_ctor_get(v___y_1005_, 13);
v___x_1012_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg___closed__1));
v___x_1013_ = l_Lean_Name_append(v___x_1012_, v_cls_1004_);
v___x_1014_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1011_, v_options_1007_, v___x_1013_);
lean_dec(v___x_1013_);
v___x_1015_ = lean_box(v___x_1014_);
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg___boxed(lean_object* v_cls_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg(v_cls_1017_, v___y_1018_);
lean_dec_ref(v___y_1018_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2(lean_object* v_cls_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg(v_cls_1021_, v___y_1024_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___boxed(lean_object* v_cls_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2(v_cls_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(lean_object* v_msg_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___f_1042_; lean_object* v___x_30799__overap_1043_; lean_object* v___x_1044_; 
v___f_1042_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_30799__overap_1043_ = lean_panic_fn(v___f_1042_, v_msg_1036_);
v___x_1044_ = lean_apply_5(v___x_30799__overap_1043_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, lean_box(0));
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___boxed(lean_object* v_msg_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v_msg_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(size_t v_sz_1052_, size_t v_i_1053_, lean_object* v_bs_1054_){
_start:
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_usize_dec_lt(v_i_1053_, v_sz_1052_);
if (v___x_1055_ == 0)
{
return v_bs_1054_;
}
else
{
lean_object* v_v_1056_; lean_object* v___x_1057_; lean_object* v_bs_x27_1058_; lean_object* v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; lean_object* v___x_1062_; 
v_v_1056_ = lean_array_uget(v_bs_1054_, v_i_1053_);
v___x_1057_ = lean_unsigned_to_nat(0u);
v_bs_x27_1058_ = lean_array_uset(v_bs_1054_, v_i_1053_, v___x_1057_);
v___x_1059_ = lean_array_get_size(v_v_1056_);
lean_dec(v_v_1056_);
v___x_1060_ = ((size_t)1ULL);
v___x_1061_ = lean_usize_add(v_i_1053_, v___x_1060_);
v___x_1062_ = lean_array_uset(v_bs_x27_1058_, v_i_1053_, v___x_1059_);
v_i_1053_ = v___x_1061_;
v_bs_1054_ = v___x_1062_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1___boxed(lean_object* v_sz_1064_, lean_object* v_i_1065_, lean_object* v_bs_1066_){
_start:
{
size_t v_sz_boxed_1067_; size_t v_i_boxed_1068_; lean_object* v_res_1069_; 
v_sz_boxed_1067_ = lean_unbox_usize(v_sz_1064_);
lean_dec(v_sz_1064_);
v_i_boxed_1068_ = lean_unbox_usize(v_i_1065_);
lean_dec(v_i_1065_);
v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_boxed_1067_, v_i_boxed_1068_, v_bs_1066_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(size_t v_sz_1070_, size_t v_i_1071_, lean_object* v_bs_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_lt(v_i_1071_, v_sz_1070_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_bs_1072_);
return v___x_1079_;
}
else
{
lean_object* v_v_1080_; lean_object* v_value_1081_; lean_object* v___x_1082_; 
v_v_1080_ = lean_array_uget_borrowed(v_bs_1072_, v_i_1071_);
v_value_1081_ = lean_ctor_get(v_v_1080_, 7);
lean_inc(v___y_1076_);
lean_inc_ref(v___y_1075_);
lean_inc(v___y_1074_);
lean_inc_ref(v___y_1073_);
lean_inc_ref(v_value_1081_);
v___x_1082_ = l_Lean_Elab_getParamRevDeps(v_value_1081_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; lean_object* v_bs_x27_1085_; size_t v___x_1086_; size_t v___x_1087_; lean_object* v___x_1088_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = lean_unsigned_to_nat(0u);
v_bs_x27_1085_ = lean_array_uset(v_bs_1072_, v_i_1071_, v___x_1084_);
v___x_1086_ = ((size_t)1ULL);
v___x_1087_ = lean_usize_add(v_i_1071_, v___x_1086_);
v___x_1088_ = lean_array_uset(v_bs_x27_1085_, v_i_1071_, v_a_1083_);
v_i_1071_ = v___x_1087_;
v_bs_1072_ = v___x_1088_;
goto _start;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec_ref(v_bs_1072_);
v_a_1090_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1082_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1082_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0___boxed(lean_object* v_sz_1098_, lean_object* v_i_1099_, lean_object* v_bs_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
size_t v_sz_boxed_1106_; size_t v_i_boxed_1107_; lean_object* v_res_1108_; 
v_sz_boxed_1106_ = lean_unbox_usize(v_sz_1098_);
lean_dec(v_sz_1098_);
v_i_boxed_1107_ = lean_unbox_usize(v_i_1099_);
lean_dec(v_i_1099_);
v_res_1108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_boxed_1106_, v_i_boxed_1107_, v_bs_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_object* v_00_u03b1_1109_, lean_object* v_x_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_apply_1(v_x_1110_, lean_box(0));
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_x_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(v_00_u03b1_1118_, v_x_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
if (lean_obj_tag(v_x_1127_) == 0)
{
return v_x_1126_;
}
else
{
lean_object* v_key_1128_; lean_object* v_value_1129_; lean_object* v_tail_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1153_; 
v_key_1128_ = lean_ctor_get(v_x_1127_, 0);
v_value_1129_ = lean_ctor_get(v_x_1127_, 1);
v_tail_1130_ = lean_ctor_get(v_x_1127_, 2);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_x_1127_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1132_ = v_x_1127_;
v_isShared_1133_ = v_isSharedCheck_1153_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_tail_1130_);
lean_inc(v_value_1129_);
lean_inc(v_key_1128_);
lean_dec(v_x_1127_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1153_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; uint64_t v___x_1135_; uint64_t v___x_1136_; uint64_t v___x_1137_; uint64_t v_fold_1138_; uint64_t v___x_1139_; uint64_t v___x_1140_; uint64_t v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; size_t v___x_1144_; size_t v___x_1145_; size_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1134_ = lean_array_get_size(v_x_1126_);
v___x_1135_ = l_Lean_ExprStructEq_hash(v_key_1128_);
v___x_1136_ = 32ULL;
v___x_1137_ = lean_uint64_shift_right(v___x_1135_, v___x_1136_);
v_fold_1138_ = lean_uint64_xor(v___x_1135_, v___x_1137_);
v___x_1139_ = 16ULL;
v___x_1140_ = lean_uint64_shift_right(v_fold_1138_, v___x_1139_);
v___x_1141_ = lean_uint64_xor(v_fold_1138_, v___x_1140_);
v___x_1142_ = lean_uint64_to_usize(v___x_1141_);
v___x_1143_ = lean_usize_of_nat(v___x_1134_);
v___x_1144_ = ((size_t)1ULL);
v___x_1145_ = lean_usize_sub(v___x_1143_, v___x_1144_);
v___x_1146_ = lean_usize_land(v___x_1142_, v___x_1145_);
v___x_1147_ = lean_array_uget_borrowed(v_x_1126_, v___x_1146_);
lean_inc(v___x_1147_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 2, v___x_1147_);
v___x_1149_ = v___x_1132_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_key_1128_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_value_1129_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_array_uset(v_x_1126_, v___x_1146_, v___x_1149_);
v_x_1126_ = v___x_1150_;
v_x_1127_ = v_tail_1130_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(lean_object* v_i_1154_, lean_object* v_source_1155_, lean_object* v_target_1156_){
_start:
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = lean_array_get_size(v_source_1155_);
v___x_1158_ = lean_nat_dec_lt(v_i_1154_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_dec_ref(v_source_1155_);
lean_dec(v_i_1154_);
return v_target_1156_;
}
else
{
lean_object* v_es_1159_; lean_object* v___x_1160_; lean_object* v_source_1161_; lean_object* v_target_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_es_1159_ = lean_array_fget(v_source_1155_, v_i_1154_);
v___x_1160_ = lean_box(0);
v_source_1161_ = lean_array_fset(v_source_1155_, v_i_1154_, v___x_1160_);
v_target_1162_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_target_1156_, v_es_1159_);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_i_1154_, v___x_1163_);
lean_dec(v_i_1154_);
v_i_1154_ = v___x_1164_;
v_source_1155_ = v_source_1161_;
v_target_1156_ = v_target_1162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(lean_object* v_data_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v_nbuckets_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1167_ = lean_array_get_size(v_data_1166_);
v___x_1168_ = lean_unsigned_to_nat(2u);
v_nbuckets_1169_ = lean_nat_mul(v___x_1167_, v___x_1168_);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_box(0);
v___x_1172_ = lean_mk_array(v_nbuckets_1169_, v___x_1171_);
v___x_1173_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v___x_1170_, v_data_1166_, v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(lean_object* v_a_1174_, lean_object* v_b_1175_, lean_object* v_x_1176_){
_start:
{
if (lean_obj_tag(v_x_1176_) == 0)
{
lean_dec(v_b_1175_);
lean_dec_ref(v_a_1174_);
return v_x_1176_;
}
else
{
lean_object* v_key_1177_; lean_object* v_value_1178_; lean_object* v_tail_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1191_; 
v_key_1177_ = lean_ctor_get(v_x_1176_, 0);
v_value_1178_ = lean_ctor_get(v_x_1176_, 1);
v_tail_1179_ = lean_ctor_get(v_x_1176_, 2);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_x_1176_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1181_ = v_x_1176_;
v_isShared_1182_ = v_isSharedCheck_1191_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_tail_1179_);
lean_inc(v_value_1178_);
lean_inc(v_key_1177_);
lean_dec(v_x_1176_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1191_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
uint8_t v___x_1183_; 
v___x_1183_ = l_Lean_ExprStructEq_beq(v_key_1177_, v_a_1174_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1174_, v_b_1175_, v_tail_1179_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 2, v___x_1184_);
v___x_1186_ = v___x_1181_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_key_1177_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_value_1178_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
else
{
lean_object* v___x_1189_; 
lean_dec(v_value_1178_);
lean_dec(v_key_1177_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v_b_1175_);
lean_ctor_set(v___x_1181_, 0, v_a_1174_);
v___x_1189_ = v___x_1181_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1174_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_b_1175_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_tail_1179_);
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
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(lean_object* v_a_1192_, lean_object* v_x_1193_){
_start:
{
if (lean_obj_tag(v_x_1193_) == 0)
{
uint8_t v___x_1194_; 
v___x_1194_ = 0;
return v___x_1194_;
}
else
{
lean_object* v_key_1195_; lean_object* v_tail_1196_; uint8_t v___x_1197_; 
v_key_1195_ = lean_ctor_get(v_x_1193_, 0);
v_tail_1196_ = lean_ctor_get(v_x_1193_, 2);
v___x_1197_ = l_Lean_ExprStructEq_beq(v_key_1195_, v_a_1192_);
if (v___x_1197_ == 0)
{
v_x_1193_ = v_tail_1196_;
goto _start;
}
else
{
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg___boxed(lean_object* v_a_1199_, lean_object* v_x_1200_){
_start:
{
uint8_t v_res_1201_; lean_object* v_r_1202_; 
v_res_1201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1199_, v_x_1200_);
lean_dec(v_x_1200_);
lean_dec_ref(v_a_1199_);
v_r_1202_ = lean_box(v_res_1201_);
return v_r_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(lean_object* v_m_1203_, lean_object* v_a_1204_, lean_object* v_b_1205_){
_start:
{
lean_object* v_size_1206_; lean_object* v_buckets_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1250_; 
v_size_1206_ = lean_ctor_get(v_m_1203_, 0);
v_buckets_1207_ = lean_ctor_get(v_m_1203_, 1);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_m_1203_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1209_ = v_m_1203_;
v_isShared_1210_ = v_isSharedCheck_1250_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_buckets_1207_);
lean_inc(v_size_1206_);
lean_dec(v_m_1203_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1250_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; uint64_t v___x_1212_; uint64_t v___x_1213_; uint64_t v___x_1214_; uint64_t v_fold_1215_; uint64_t v___x_1216_; uint64_t v___x_1217_; uint64_t v___x_1218_; size_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; lean_object* v_bkt_1224_; uint8_t v___x_1225_; 
v___x_1211_ = lean_array_get_size(v_buckets_1207_);
v___x_1212_ = l_Lean_ExprStructEq_hash(v_a_1204_);
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
v_bkt_1224_ = lean_array_uget_borrowed(v_buckets_1207_, v___x_1223_);
v___x_1225_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1204_, v_bkt_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v_size_x27_1227_; lean_object* v___x_1228_; lean_object* v_buckets_x27_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1226_ = lean_unsigned_to_nat(1u);
v_size_x27_1227_ = lean_nat_add(v_size_1206_, v___x_1226_);
lean_dec(v_size_1206_);
lean_inc(v_bkt_1224_);
v___x_1228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1228_, 0, v_a_1204_);
lean_ctor_set(v___x_1228_, 1, v_b_1205_);
lean_ctor_set(v___x_1228_, 2, v_bkt_1224_);
v_buckets_x27_1229_ = lean_array_uset(v_buckets_1207_, v___x_1223_, v___x_1228_);
v___x_1230_ = lean_unsigned_to_nat(4u);
v___x_1231_ = lean_nat_mul(v_size_x27_1227_, v___x_1230_);
v___x_1232_ = lean_unsigned_to_nat(3u);
v___x_1233_ = lean_nat_div(v___x_1231_, v___x_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_array_get_size(v_buckets_x27_1229_);
v___x_1235_ = lean_nat_dec_le(v___x_1233_, v___x_1234_);
lean_dec(v___x_1233_);
if (v___x_1235_ == 0)
{
lean_object* v_val_1236_; lean_object* v___x_1238_; 
v_val_1236_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_buckets_x27_1229_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v_val_1236_);
lean_ctor_set(v___x_1209_, 0, v_size_x27_1227_);
v___x_1238_ = v___x_1209_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_size_x27_1227_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_val_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
else
{
lean_object* v___x_1241_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v_buckets_x27_1229_);
lean_ctor_set(v___x_1209_, 0, v_size_x27_1227_);
v___x_1241_ = v___x_1209_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_size_x27_1227_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_buckets_x27_1229_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
else
{
lean_object* v___x_1243_; lean_object* v_buckets_x27_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
lean_inc(v_bkt_1224_);
v___x_1243_ = lean_box(0);
v_buckets_x27_1244_ = lean_array_uset(v_buckets_1207_, v___x_1223_, v___x_1243_);
v___x_1245_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1204_, v_b_1205_, v_bkt_1224_);
v___x_1246_ = lean_array_uset(v_buckets_x27_1244_, v___x_1223_, v___x_1245_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v___x_1246_);
v___x_1248_ = v___x_1209_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_size_1206_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(lean_object* v_a_1251_, lean_object* v_e_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1255_ = lean_st_ref_take(v_a_1251_);
v___x_1256_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___x_1255_, v_e_1252_, v_a_1253_);
v___x_1257_ = lean_st_ref_set(v_a_1251_, v___x_1256_);
v___x_1258_ = lean_box(0);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed(lean_object* v_a_1259_, lean_object* v_e_1260_, lean_object* v_a_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(v_a_1259_, v_e_1260_, v_a_1261_);
lean_dec(v_a_1259_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(lean_object* v_k_1264_, lean_object* v___y_1265_, lean_object* v_b_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_apply_7(v_k_1264_, v_b_1266_, v___y_1265_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, lean_box(0));
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed(lean_object* v_k_1273_, lean_object* v___y_1274_, lean_object* v_b_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(v_k_1273_, v___y_1274_, v_b_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(lean_object* v_name_1282_, uint8_t v_bi_1283_, lean_object* v_type_1284_, lean_object* v_k_1285_, uint8_t v_kind_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___f_1293_; lean_object* v___x_1294_; 
v___f_1293_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1293_, 0, v_k_1285_);
lean_closure_set(v___f_1293_, 1, v___y_1287_);
v___x_1294_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1282_, v_bi_1283_, v_type_1284_, v___f_1293_, v_kind_1286_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1294_) == 0)
{
return v___x_1294_;
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___boxed(lean_object* v_name_1303_, lean_object* v_bi_1304_, lean_object* v_type_1305_, lean_object* v_k_1306_, lean_object* v_kind_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
uint8_t v_bi_boxed_1314_; uint8_t v_kind_boxed_1315_; lean_object* v_res_1316_; 
v_bi_boxed_1314_ = lean_unbox(v_bi_1304_);
v_kind_boxed_1315_ = lean_unbox(v_kind_1307_);
v_res_1316_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_1303_, v_bi_boxed_1314_, v_type_1305_, v_k_1306_, v_kind_boxed_1315_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(lean_object* v___x_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1317_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed(lean_object* v___x_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(v___x_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(lean_object* v_name_1331_, lean_object* v_type_1332_, lean_object* v_val_1333_, lean_object* v_k_1334_, uint8_t v_nondep_1335_, uint8_t v_kind_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___f_1343_; lean_object* v___x_1344_; 
v___f_1343_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1343_, 0, v_k_1334_);
lean_closure_set(v___f_1343_, 1, v___y_1337_);
v___x_1344_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1331_, v_type_1332_, v_val_1333_, v___f_1343_, v_nondep_1335_, v_kind_1336_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1344_) == 0)
{
return v___x_1344_;
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg___boxed(lean_object* v_name_1353_, lean_object* v_type_1354_, lean_object* v_val_1355_, lean_object* v_k_1356_, lean_object* v_nondep_1357_, lean_object* v_kind_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
uint8_t v_nondep_boxed_1365_; uint8_t v_kind_boxed_1366_; lean_object* v_res_1367_; 
v_nondep_boxed_1365_ = lean_unbox(v_nondep_1357_);
v_kind_boxed_1366_ = lean_unbox(v_kind_1358_);
v_res_1367_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_1353_, v_type_1354_, v_val_1355_, v_k_1356_, v_nondep_boxed_1365_, v_kind_boxed_1366_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_object* v_00_u03b1_1368_, lean_object* v_x_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_apply_1(v_x_1369_, lean_box(0));
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_x_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(v_00_u03b1_1377_, v_x_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1384_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = l_Lean_maxRecDepthErrorMessage;
v___x_1391_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3);
v___x_1393_ = l_Lean_MessageData_ofFormat(v___x_1392_);
return v___x_1393_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4);
v___x_1395_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2));
v___x_1396_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
lean_ctor_set(v___x_1396_, 1, v___x_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(lean_object* v_ref_1397_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5);
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_ref_1397_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1402_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(lean_object* v_x_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___y_1413_; lean_object* v_fileName_1422_; lean_object* v_fileMap_1423_; lean_object* v_options_1424_; lean_object* v_currRecDepth_1425_; lean_object* v_maxRecDepth_1426_; lean_object* v_ref_1427_; lean_object* v_currNamespace_1428_; lean_object* v_openDecls_1429_; lean_object* v_initHeartbeats_1430_; lean_object* v_maxHeartbeats_1431_; lean_object* v_quotContext_1432_; lean_object* v_currMacroScope_1433_; uint8_t v_diag_1434_; lean_object* v_cancelTk_x3f_1435_; uint8_t v_suppressElabErrors_1436_; lean_object* v_inheritedTraceOptions_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1449_; 
v_fileName_1422_ = lean_ctor_get(v___y_1409_, 0);
v_fileMap_1423_ = lean_ctor_get(v___y_1409_, 1);
v_options_1424_ = lean_ctor_get(v___y_1409_, 2);
v_currRecDepth_1425_ = lean_ctor_get(v___y_1409_, 3);
v_maxRecDepth_1426_ = lean_ctor_get(v___y_1409_, 4);
v_ref_1427_ = lean_ctor_get(v___y_1409_, 5);
v_currNamespace_1428_ = lean_ctor_get(v___y_1409_, 6);
v_openDecls_1429_ = lean_ctor_get(v___y_1409_, 7);
v_initHeartbeats_1430_ = lean_ctor_get(v___y_1409_, 8);
v_maxHeartbeats_1431_ = lean_ctor_get(v___y_1409_, 9);
v_quotContext_1432_ = lean_ctor_get(v___y_1409_, 10);
v_currMacroScope_1433_ = lean_ctor_get(v___y_1409_, 11);
v_diag_1434_ = lean_ctor_get_uint8(v___y_1409_, sizeof(void*)*14);
v_cancelTk_x3f_1435_ = lean_ctor_get(v___y_1409_, 12);
v_suppressElabErrors_1436_ = lean_ctor_get_uint8(v___y_1409_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1437_ = lean_ctor_get(v___y_1409_, 13);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___y_1409_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1439_ = v___y_1409_;
v_isShared_1440_ = v_isSharedCheck_1449_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_inheritedTraceOptions_1437_);
lean_inc(v_cancelTk_x3f_1435_);
lean_inc(v_currMacroScope_1433_);
lean_inc(v_quotContext_1432_);
lean_inc(v_maxHeartbeats_1431_);
lean_inc(v_initHeartbeats_1430_);
lean_inc(v_openDecls_1429_);
lean_inc(v_currNamespace_1428_);
lean_inc(v_ref_1427_);
lean_inc(v_maxRecDepth_1426_);
lean_inc(v_currRecDepth_1425_);
lean_inc(v_options_1424_);
lean_inc(v_fileMap_1423_);
lean_inc(v_fileName_1422_);
lean_dec(v___y_1409_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1449_;
goto v_resetjp_1438_;
}
v___jp_1412_:
{
if (lean_obj_tag(v___y_1413_) == 0)
{
return v___y_1413_;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_a_1414_ = lean_ctor_get(v___y_1413_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___y_1413_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___y_1413_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___y_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
v_resetjp_1438_:
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_nat_dec_eq(v_currRecDepth_1425_, v_maxRecDepth_1426_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = lean_nat_add(v_currRecDepth_1425_, v___x_1442_);
lean_dec(v_currRecDepth_1425_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 3, v___x_1443_);
v___x_1445_ = v___x_1439_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_fileName_1422_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_fileMap_1423_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_options_1424_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_maxRecDepth_1426_);
lean_ctor_set(v_reuseFailAlloc_1447_, 5, v_ref_1427_);
lean_ctor_set(v_reuseFailAlloc_1447_, 6, v_currNamespace_1428_);
lean_ctor_set(v_reuseFailAlloc_1447_, 7, v_openDecls_1429_);
lean_ctor_set(v_reuseFailAlloc_1447_, 8, v_initHeartbeats_1430_);
lean_ctor_set(v_reuseFailAlloc_1447_, 9, v_maxHeartbeats_1431_);
lean_ctor_set(v_reuseFailAlloc_1447_, 10, v_quotContext_1432_);
lean_ctor_set(v_reuseFailAlloc_1447_, 11, v_currMacroScope_1433_);
lean_ctor_set(v_reuseFailAlloc_1447_, 12, v_cancelTk_x3f_1435_);
lean_ctor_set(v_reuseFailAlloc_1447_, 13, v_inheritedTraceOptions_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*14, v_diag_1434_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*14 + 1, v_suppressElabErrors_1436_);
v___x_1445_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_apply_6(v_x_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___x_1445_, v___y_1410_, lean_box(0));
v___y_1413_ = v___x_1446_;
goto v___jp_1412_;
}
}
else
{
lean_object* v___x_1448_; 
lean_del_object(v___x_1439_);
lean_dec_ref(v_inheritedTraceOptions_1437_);
lean_dec(v_cancelTk_x3f_1435_);
lean_dec(v_currMacroScope_1433_);
lean_dec(v_quotContext_1432_);
lean_dec(v_maxHeartbeats_1431_);
lean_dec(v_initHeartbeats_1430_);
lean_dec(v_openDecls_1429_);
lean_dec(v_currNamespace_1428_);
lean_dec(v_maxRecDepth_1426_);
lean_dec(v_currRecDepth_1425_);
lean_dec_ref(v_options_1424_);
lean_dec_ref(v_fileMap_1423_);
lean_dec_ref(v_fileName_1422_);
lean_dec(v___y_1410_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v_x_1405_);
v___x_1448_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1427_);
v___y_1413_ = v___x_1448_;
goto v___jp_1412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object* v_a_1458_, lean_object* v_x_1459_){
_start:
{
if (lean_obj_tag(v_x_1459_) == 0)
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_box(0);
return v___x_1460_;
}
else
{
lean_object* v_key_1461_; lean_object* v_value_1462_; lean_object* v_tail_1463_; uint8_t v___x_1464_; 
v_key_1461_ = lean_ctor_get(v_x_1459_, 0);
v_value_1462_ = lean_ctor_get(v_x_1459_, 1);
v_tail_1463_ = lean_ctor_get(v_x_1459_, 2);
v___x_1464_ = l_Lean_ExprStructEq_beq(v_key_1461_, v_a_1458_);
if (v___x_1464_ == 0)
{
v_x_1459_ = v_tail_1463_;
goto _start;
}
else
{
lean_object* v___x_1466_; 
lean_inc(v_value_1462_);
v___x_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_value_1462_);
return v___x_1466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object* v_a_1467_, lean_object* v_x_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1467_, v_x_1468_);
lean_dec(v_x_1468_);
lean_dec_ref(v_a_1467_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_m_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_buckets_1472_; lean_object* v___x_1473_; uint64_t v___x_1474_; uint64_t v___x_1475_; uint64_t v___x_1476_; uint64_t v_fold_1477_; uint64_t v___x_1478_; uint64_t v___x_1479_; uint64_t v___x_1480_; size_t v___x_1481_; size_t v___x_1482_; size_t v___x_1483_; size_t v___x_1484_; size_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_buckets_1472_ = lean_ctor_get(v_m_1470_, 1);
v___x_1473_ = lean_array_get_size(v_buckets_1472_);
v___x_1474_ = l_Lean_ExprStructEq_hash(v_a_1471_);
v___x_1475_ = 32ULL;
v___x_1476_ = lean_uint64_shift_right(v___x_1474_, v___x_1475_);
v_fold_1477_ = lean_uint64_xor(v___x_1474_, v___x_1476_);
v___x_1478_ = 16ULL;
v___x_1479_ = lean_uint64_shift_right(v_fold_1477_, v___x_1478_);
v___x_1480_ = lean_uint64_xor(v_fold_1477_, v___x_1479_);
v___x_1481_ = lean_uint64_to_usize(v___x_1480_);
v___x_1482_ = lean_usize_of_nat(v___x_1473_);
v___x_1483_ = ((size_t)1ULL);
v___x_1484_ = lean_usize_sub(v___x_1482_, v___x_1483_);
v___x_1485_ = lean_usize_land(v___x_1481_, v___x_1484_);
v___x_1486_ = lean_array_uget_borrowed(v_buckets_1472_, v___x_1485_);
v___x_1487_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1471_, v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_m_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_1488_, v_a_1489_);
lean_dec_ref(v_a_1489_);
lean_dec_ref(v_m_1488_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1493_, lean_object* v_pre_1494_, lean_object* v_post_1495_, uint8_t v_usedLetOnly_1496_, uint8_t v_skipConstInApp_1497_, uint8_t v_skipInstances_1498_, lean_object* v_body_1499_, lean_object* v_x_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_array_push(v_fvars_1493_, v_x_1500_);
v___x_1508_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1494_, v_post_1495_, v_usedLetOnly_1496_, v_skipConstInApp_1497_, v_skipInstances_1498_, v___x_1507_, v_body_1499_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1509_, lean_object* v_pre_1510_, lean_object* v_post_1511_, lean_object* v_usedLetOnly_1512_, lean_object* v_skipConstInApp_1513_, lean_object* v_skipInstances_1514_, lean_object* v_body_1515_, lean_object* v_x_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v_usedLetOnly_boxed_1523_; uint8_t v_skipConstInApp_boxed_1524_; uint8_t v_skipInstances_boxed_1525_; lean_object* v_res_1526_; 
v_usedLetOnly_boxed_1523_ = lean_unbox(v_usedLetOnly_1512_);
v_skipConstInApp_boxed_1524_ = lean_unbox(v_skipConstInApp_1513_);
v_skipInstances_boxed_1525_ = lean_unbox(v_skipInstances_1514_);
v_res_1526_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1509_, v_pre_1510_, v_post_1511_, v_usedLetOnly_boxed_1523_, v_skipConstInApp_boxed_1524_, v_skipInstances_boxed_1525_, v_body_1515_, v_x_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1527_, lean_object* v_post_1528_, uint8_t v_usedLetOnly_1529_, uint8_t v_skipConstInApp_1530_, uint8_t v_skipInstances_1531_, lean_object* v_e_1532_, lean_object* v_a_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; 
lean_inc_ref(v_post_1528_);
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1536_);
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
lean_inc_ref(v_e_1532_);
v___x_1539_ = lean_apply_6(v_post_1528_, v_e_1532_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, lean_box(0));
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1558_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1558_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1558_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
switch(lean_obj_tag(v_a_1540_))
{
case 0:
{
lean_object* v_e_1544_; lean_object* v___x_1546_; 
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_e_1532_);
lean_dec_ref(v_post_1528_);
lean_dec_ref(v_pre_1527_);
v_e_1544_ = lean_ctor_get(v_a_1540_, 0);
lean_inc_ref(v_e_1544_);
lean_dec_ref(v_a_1540_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v_e_1544_);
v___x_1546_ = v___x_1542_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_e_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
case 1:
{
lean_object* v_e_1548_; lean_object* v___x_1549_; 
lean_del_object(v___x_1542_);
lean_dec_ref(v_e_1532_);
v_e_1548_ = lean_ctor_get(v_a_1540_, 0);
lean_inc_ref(v_e_1548_);
lean_dec_ref(v_a_1540_);
v___x_1549_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1527_, v_post_1528_, v_usedLetOnly_1529_, v_skipConstInApp_1530_, v_skipInstances_1531_, v_e_1548_, v_a_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
return v___x_1549_;
}
default: 
{
lean_object* v_e_x3f_1550_; 
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_post_1528_);
lean_dec_ref(v_pre_1527_);
v_e_x3f_1550_ = lean_ctor_get(v_a_1540_, 0);
lean_inc(v_e_x3f_1550_);
lean_dec_ref(v_a_1540_);
if (lean_obj_tag(v_e_x3f_1550_) == 0)
{
lean_object* v___x_1552_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v_e_1532_);
v___x_1552_ = v___x_1542_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_e_1532_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
else
{
lean_object* v_val_1554_; lean_object* v___x_1556_; 
lean_dec_ref(v_e_1532_);
v_val_1554_ = lean_ctor_get(v_e_x3f_1550_, 0);
lean_inc(v_val_1554_);
lean_dec_ref(v_e_x3f_1550_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v_val_1554_);
v___x_1556_ = v___x_1542_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_val_1554_);
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
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_e_1532_);
lean_dec_ref(v_post_1528_);
lean_dec_ref(v_pre_1527_);
v_a_1559_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1539_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1539_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1567_, lean_object* v_post_1568_, uint8_t v_usedLetOnly_1569_, uint8_t v_skipConstInApp_1570_, uint8_t v_skipInstances_1571_, lean_object* v_fvars_1572_, lean_object* v_e_1573_, lean_object* v_a_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
if (lean_obj_tag(v_e_1573_) == 6)
{
lean_object* v_binderName_1580_; lean_object* v_binderType_1581_; lean_object* v_body_1582_; uint8_t v_binderInfo_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v_binderName_1580_ = lean_ctor_get(v_e_1573_, 0);
lean_inc(v_binderName_1580_);
v_binderType_1581_ = lean_ctor_get(v_e_1573_, 1);
lean_inc_ref(v_binderType_1581_);
v_body_1582_ = lean_ctor_get(v_e_1573_, 2);
lean_inc_ref(v_body_1582_);
v_binderInfo_1583_ = lean_ctor_get_uint8(v_e_1573_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1573_);
v___x_1584_ = lean_expr_instantiate_rev(v_binderType_1581_, v_fvars_1572_);
lean_dec_ref(v_binderType_1581_);
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
lean_inc(v___y_1576_);
lean_inc_ref(v___y_1575_);
lean_inc(v_a_1574_);
lean_inc_ref(v_post_1568_);
lean_inc_ref(v_pre_1567_);
v___x_1585_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1567_, v_post_1568_, v_usedLetOnly_1569_, v_skipConstInApp_1570_, v_skipInstances_1571_, v___x_1584_, v_a_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___f_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v___x_1585_);
v___x_1587_ = lean_box(v_usedLetOnly_1569_);
v___x_1588_ = lean_box(v_skipConstInApp_1570_);
v___x_1589_ = lean_box(v_skipInstances_1571_);
v___f_1590_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1590_, 0, v_fvars_1572_);
lean_closure_set(v___f_1590_, 1, v_pre_1567_);
lean_closure_set(v___f_1590_, 2, v_post_1568_);
lean_closure_set(v___f_1590_, 3, v___x_1587_);
lean_closure_set(v___f_1590_, 4, v___x_1588_);
lean_closure_set(v___f_1590_, 5, v___x_1589_);
lean_closure_set(v___f_1590_, 6, v_body_1582_);
v___x_1591_ = 0;
v___x_1592_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1580_, v_binderInfo_1583_, v_a_1586_, v___f_1590_, v___x_1591_, v_a_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
return v___x_1592_;
}
else
{
lean_dec_ref(v_body_1582_);
lean_dec(v_binderName_1580_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_fvars_1572_);
lean_dec_ref(v_post_1568_);
lean_dec_ref(v_pre_1567_);
return v___x_1585_;
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_expr_instantiate_rev(v_e_1573_, v_fvars_1572_);
lean_dec_ref(v_e_1573_);
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
lean_inc(v___y_1576_);
lean_inc_ref(v___y_1575_);
lean_inc(v_a_1574_);
lean_inc_ref(v_post_1568_);
lean_inc_ref(v_pre_1567_);
v___x_1594_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1567_, v_post_1568_, v_usedLetOnly_1569_, v_skipConstInApp_1570_, v_skipInstances_1571_, v___x_1593_, v_a_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; uint8_t v___x_1596_; uint8_t v___x_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref(v___x_1594_);
v___x_1596_ = 0;
v___x_1597_ = 1;
v___x_1598_ = 1;
v___x_1599_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1572_, v_a_1595_, v___x_1596_, v_usedLetOnly_1569_, v___x_1596_, v___x_1597_, v___x_1598_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec_ref(v_fvars_1572_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1601_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref(v___x_1599_);
v___x_1601_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1567_, v_post_1568_, v_usedLetOnly_1569_, v_skipConstInApp_1570_, v_skipInstances_1571_, v_a_1600_, v_a_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
return v___x_1601_;
}
else
{
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_post_1568_);
lean_dec_ref(v_pre_1567_);
return v___x_1599_;
}
}
else
{
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_fvars_1572_);
lean_dec_ref(v_post_1568_);
lean_dec_ref(v_pre_1567_);
return v___x_1594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1602_, lean_object* v_pre_1603_, lean_object* v_post_1604_, uint8_t v_usedLetOnly_1605_, uint8_t v_skipConstInApp_1606_, uint8_t v_skipInstances_1607_, lean_object* v_body_1608_, lean_object* v_x_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_array_push(v_fvars_1602_, v_x_1609_);
v___x_1617_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1603_, v_post_1604_, v_usedLetOnly_1605_, v_skipConstInApp_1606_, v_skipInstances_1607_, v___x_1616_, v_body_1608_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1618_, lean_object* v_pre_1619_, lean_object* v_post_1620_, lean_object* v_usedLetOnly_1621_, lean_object* v_skipConstInApp_1622_, lean_object* v_skipInstances_1623_, lean_object* v_body_1624_, lean_object* v_x_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
uint8_t v_usedLetOnly_boxed_1632_; uint8_t v_skipConstInApp_boxed_1633_; uint8_t v_skipInstances_boxed_1634_; lean_object* v_res_1635_; 
v_usedLetOnly_boxed_1632_ = lean_unbox(v_usedLetOnly_1621_);
v_skipConstInApp_boxed_1633_ = lean_unbox(v_skipConstInApp_1622_);
v_skipInstances_boxed_1634_ = lean_unbox(v_skipInstances_1623_);
v_res_1635_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1618_, v_pre_1619_, v_post_1620_, v_usedLetOnly_boxed_1632_, v_skipConstInApp_boxed_1633_, v_skipInstances_boxed_1634_, v_body_1624_, v_x_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1636_, lean_object* v_post_1637_, uint8_t v_usedLetOnly_1638_, uint8_t v_skipConstInApp_1639_, uint8_t v_skipInstances_1640_, lean_object* v_fvars_1641_, lean_object* v_e_1642_, lean_object* v_a_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
if (lean_obj_tag(v_e_1642_) == 8)
{
lean_object* v_declName_1649_; lean_object* v_type_1650_; lean_object* v_value_1651_; lean_object* v_body_1652_; uint8_t v_nondep_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_declName_1649_ = lean_ctor_get(v_e_1642_, 0);
lean_inc(v_declName_1649_);
v_type_1650_ = lean_ctor_get(v_e_1642_, 1);
lean_inc_ref(v_type_1650_);
v_value_1651_ = lean_ctor_get(v_e_1642_, 2);
lean_inc_ref(v_value_1651_);
v_body_1652_ = lean_ctor_get(v_e_1642_, 3);
lean_inc_ref(v_body_1652_);
v_nondep_1653_ = lean_ctor_get_uint8(v_e_1642_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1642_);
v___x_1654_ = lean_expr_instantiate_rev(v_type_1650_, v_fvars_1641_);
lean_dec_ref(v_type_1650_);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v_a_1643_);
lean_inc_ref(v_post_1637_);
lean_inc_ref(v_pre_1636_);
v___x_1655_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1636_, v_post_1637_, v_usedLetOnly_1638_, v_skipConstInApp_1639_, v_skipInstances_1640_, v___x_1654_, v_a_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref(v___x_1655_);
v___x_1657_ = lean_expr_instantiate_rev(v_value_1651_, v_fvars_1641_);
lean_dec_ref(v_value_1651_);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v_a_1643_);
lean_inc_ref(v_post_1637_);
lean_inc_ref(v_pre_1636_);
v___x_1658_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1636_, v_post_1637_, v_usedLetOnly_1638_, v_skipConstInApp_1639_, v_skipInstances_1640_, v___x_1657_, v_a_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___f_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref(v___x_1658_);
v___x_1660_ = lean_box(v_usedLetOnly_1638_);
v___x_1661_ = lean_box(v_skipConstInApp_1639_);
v___x_1662_ = lean_box(v_skipInstances_1640_);
v___f_1663_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1663_, 0, v_fvars_1641_);
lean_closure_set(v___f_1663_, 1, v_pre_1636_);
lean_closure_set(v___f_1663_, 2, v_post_1637_);
lean_closure_set(v___f_1663_, 3, v___x_1660_);
lean_closure_set(v___f_1663_, 4, v___x_1661_);
lean_closure_set(v___f_1663_, 5, v___x_1662_);
lean_closure_set(v___f_1663_, 6, v_body_1652_);
v___x_1664_ = 0;
v___x_1665_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1649_, v_a_1656_, v_a_1659_, v___f_1663_, v_nondep_1653_, v___x_1664_, v_a_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
return v___x_1665_;
}
else
{
lean_dec(v_a_1656_);
lean_dec_ref(v_body_1652_);
lean_dec(v_declName_1649_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_fvars_1641_);
lean_dec_ref(v_post_1637_);
lean_dec_ref(v_pre_1636_);
return v___x_1658_;
}
}
else
{
lean_dec_ref(v_body_1652_);
lean_dec_ref(v_value_1651_);
lean_dec(v_declName_1649_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_fvars_1641_);
lean_dec_ref(v_post_1637_);
lean_dec_ref(v_pre_1636_);
return v___x_1655_;
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_expr_instantiate_rev(v_e_1642_, v_fvars_1641_);
lean_dec_ref(v_e_1642_);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v_a_1643_);
lean_inc_ref(v_post_1637_);
lean_inc_ref(v_pre_1636_);
v___x_1667_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1636_, v_post_1637_, v_usedLetOnly_1638_, v_skipConstInApp_1639_, v_skipInstances_1640_, v___x_1666_, v_a_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; uint8_t v___x_1669_; uint8_t v___x_1670_; lean_object* v___x_1671_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref(v___x_1667_);
v___x_1669_ = 0;
v___x_1670_ = 1;
v___x_1671_ = l_Lean_Meta_mkLetFVars(v_fvars_1641_, v_a_1668_, v_usedLetOnly_1638_, v___x_1669_, v___x_1670_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec_ref(v_fvars_1641_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1673_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref(v___x_1671_);
v___x_1673_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1636_, v_post_1637_, v_usedLetOnly_1638_, v_skipConstInApp_1639_, v_skipInstances_1640_, v_a_1672_, v_a_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
return v___x_1673_;
}
else
{
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_post_1637_);
lean_dec_ref(v_pre_1636_);
return v___x_1671_;
}
}
else
{
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_fvars_1641_);
lean_dec_ref(v_post_1637_);
lean_dec_ref(v_pre_1636_);
return v___x_1667_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1674_; lean_object* v_dummy_1675_; 
v___x_1674_ = lean_box(0);
v_dummy_1675_ = l_Lean_Expr_sort___override(v___x_1674_);
return v_dummy_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1676_, lean_object* v_post_1677_, uint8_t v_usedLetOnly_1678_, uint8_t v_skipConstInApp_1679_, uint8_t v_skipInstances_1680_, size_t v_sz_1681_, size_t v_i_1682_, lean_object* v_bs_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_usize_dec_lt(v_i_1682_, v_sz_1681_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v_post_1677_);
lean_dec_ref(v_pre_1676_);
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_bs_1683_);
return v___x_1691_;
}
else
{
lean_object* v_v_1692_; lean_object* v___x_1693_; 
v_v_1692_ = lean_array_uget_borrowed(v_bs_1683_, v_i_1682_);
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
lean_inc(v___y_1684_);
lean_inc(v_v_1692_);
lean_inc_ref(v_post_1677_);
lean_inc_ref(v_pre_1676_);
v___x_1693_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1676_, v_post_1677_, v_usedLetOnly_1678_, v_skipConstInApp_1679_, v_skipInstances_1680_, v_v_1692_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1695_; lean_object* v_bs_x27_1696_; size_t v___x_1697_; size_t v___x_1698_; lean_object* v___x_1699_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = lean_unsigned_to_nat(0u);
v_bs_x27_1696_ = lean_array_uset(v_bs_1683_, v_i_1682_, v___x_1695_);
v___x_1697_ = ((size_t)1ULL);
v___x_1698_ = lean_usize_add(v_i_1682_, v___x_1697_);
v___x_1699_ = lean_array_uset(v_bs_x27_1696_, v_i_1682_, v_a_1694_);
v_i_1682_ = v___x_1698_;
v_bs_1683_ = v___x_1699_;
goto _start;
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v_bs_1683_);
lean_dec_ref(v_post_1677_);
lean_dec_ref(v_pre_1676_);
v_a_1701_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1693_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1693_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1709_, lean_object* v_post_1710_, uint8_t v_usedLetOnly_1711_, uint8_t v_skipConstInApp_1712_, uint8_t v_skipInstances_1713_, lean_object* v___x_1714_, lean_object* v___y_1715_, lean_object* v_b_1716_, lean_object* v_a_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1709_, v_post_1710_, v_usedLetOnly_1711_, v_skipConstInApp_1712_, v_skipInstances_1713_, v___x_1714_, v___y_1715_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1733_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1728_ = lean_array_fset(v_b_1716_, v_a_1717_, v_a_1724_);
v___x_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1729_);
v___x_1731_ = v___x_1726_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec_ref(v_b_1716_);
v_a_1734_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1723_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1723_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1742_, lean_object* v_post_1743_, lean_object* v_usedLetOnly_1744_, lean_object* v_skipConstInApp_1745_, lean_object* v_skipInstances_1746_, lean_object* v___x_1747_, lean_object* v___y_1748_, lean_object* v_b_1749_, lean_object* v_a_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
uint8_t v_usedLetOnly_boxed_1756_; uint8_t v_skipConstInApp_boxed_1757_; uint8_t v_skipInstances_boxed_1758_; lean_object* v_res_1759_; 
v_usedLetOnly_boxed_1756_ = lean_unbox(v_usedLetOnly_1744_);
v_skipConstInApp_boxed_1757_ = lean_unbox(v_skipConstInApp_1745_);
v_skipInstances_boxed_1758_ = lean_unbox(v_skipInstances_1746_);
v_res_1759_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1742_, v_post_1743_, v_usedLetOnly_boxed_1756_, v_skipConstInApp_boxed_1757_, v_skipInstances_boxed_1758_, v___x_1747_, v___y_1748_, v_b_1749_, v_a_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v_a_1750_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1760_, lean_object* v___x_1761_, lean_object* v_pre_1762_, lean_object* v_post_1763_, uint8_t v_usedLetOnly_1764_, uint8_t v_skipConstInApp_1765_, uint8_t v_skipInstances_1766_, lean_object* v_a_1767_, lean_object* v_b_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v___y_1776_; uint8_t v___x_1799_; 
v___x_1799_ = lean_nat_dec_lt(v_a_1767_, v_upperBound_1760_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; 
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec(v_a_1767_);
lean_dec_ref(v_post_1763_);
lean_dec_ref(v_pre_1762_);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v_b_1768_);
return v___x_1800_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1801_ = lean_array_fget_borrowed(v_b_1768_, v_a_1767_);
v___x_1802_ = lean_array_get_size(v___x_1761_);
v___x_1803_ = lean_nat_dec_lt(v_a_1767_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___f_1807_; 
lean_inc(v___x_1801_);
v___x_1804_ = lean_box(v_usedLetOnly_1764_);
v___x_1805_ = lean_box(v_skipConstInApp_1765_);
v___x_1806_ = lean_box(v_skipInstances_1766_);
lean_inc(v_a_1767_);
lean_inc(v___y_1769_);
lean_inc_ref(v_post_1763_);
lean_inc_ref(v_pre_1762_);
v___f_1807_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1807_, 0, v_pre_1762_);
lean_closure_set(v___f_1807_, 1, v_post_1763_);
lean_closure_set(v___f_1807_, 2, v___x_1804_);
lean_closure_set(v___f_1807_, 3, v___x_1805_);
lean_closure_set(v___f_1807_, 4, v___x_1806_);
lean_closure_set(v___f_1807_, 5, v___x_1801_);
lean_closure_set(v___f_1807_, 6, v___y_1769_);
lean_closure_set(v___f_1807_, 7, v_b_1768_);
lean_closure_set(v___f_1807_, 8, v_a_1767_);
v___y_1776_ = v___f_1807_;
goto v___jp_1775_;
}
else
{
lean_object* v___x_1808_; uint8_t v_isInstance_1809_; 
v___x_1808_ = lean_array_fget_borrowed(v___x_1761_, v_a_1767_);
v_isInstance_1809_ = lean_ctor_get_uint8(v___x_1808_, sizeof(void*)*1 + 4);
if (v_isInstance_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___f_1813_; 
lean_inc(v___x_1801_);
v___x_1810_ = lean_box(v_usedLetOnly_1764_);
v___x_1811_ = lean_box(v_skipConstInApp_1765_);
v___x_1812_ = lean_box(v_skipInstances_1766_);
lean_inc(v_a_1767_);
lean_inc(v___y_1769_);
lean_inc_ref(v_post_1763_);
lean_inc_ref(v_pre_1762_);
v___f_1813_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1813_, 0, v_pre_1762_);
lean_closure_set(v___f_1813_, 1, v_post_1763_);
lean_closure_set(v___f_1813_, 2, v___x_1810_);
lean_closure_set(v___f_1813_, 3, v___x_1811_);
lean_closure_set(v___f_1813_, 4, v___x_1812_);
lean_closure_set(v___f_1813_, 5, v___x_1801_);
lean_closure_set(v___f_1813_, 6, v___y_1769_);
lean_closure_set(v___f_1813_, 7, v_b_1768_);
lean_closure_set(v___f_1813_, 8, v_a_1767_);
v___y_1776_ = v___f_1813_;
goto v___jp_1775_;
}
else
{
lean_object* v___x_1814_; lean_object* v___f_1815_; 
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v_b_1768_);
v___f_1815_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1815_, 0, v___x_1814_);
v___y_1776_ = v___f_1815_;
goto v___jp_1775_;
}
}
}
v___jp_1775_:
{
lean_object* v___x_1777_; 
lean_inc(v___y_1773_);
lean_inc_ref(v___y_1772_);
lean_inc(v___y_1771_);
lean_inc_ref(v___y_1770_);
v___x_1777_ = lean_apply_5(v___y_1776_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, lean_box(0));
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1790_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1790_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1790_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
if (lean_obj_tag(v_a_1778_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; 
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec(v_a_1767_);
lean_dec_ref(v_post_1763_);
lean_dec_ref(v_pre_1762_);
v_a_1782_ = lean_ctor_get(v_a_1778_, 0);
lean_inc(v_a_1782_);
lean_dec_ref(v_a_1778_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_a_1782_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_del_object(v___x_1780_);
v_a_1786_ = lean_ctor_get(v_a_1778_, 0);
lean_inc(v_a_1786_);
lean_dec_ref(v_a_1778_);
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_nat_add(v_a_1767_, v___x_1787_);
lean_dec(v_a_1767_);
v_a_1767_ = v___x_1788_;
v_b_1768_ = v_a_1786_;
goto _start;
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec(v_a_1767_);
lean_dec_ref(v_post_1763_);
lean_dec_ref(v_pre_1762_);
v_a_1791_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1777_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1777_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1816_, lean_object* v_pre_1817_, lean_object* v_post_1818_, uint8_t v_usedLetOnly_1819_, uint8_t v_skipConstInApp_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_f_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; 
if (lean_obj_tag(v_x_1821_) == 5)
{
lean_object* v_fn_1879_; lean_object* v_arg_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_fn_1879_ = lean_ctor_get(v_x_1821_, 0);
lean_inc_ref(v_fn_1879_);
v_arg_1880_ = lean_ctor_get(v_x_1821_, 1);
lean_inc_ref(v_arg_1880_);
lean_dec_ref(v_x_1821_);
v___x_1881_ = lean_array_set(v_x_1822_, v_x_1823_, v_arg_1880_);
v___x_1882_ = lean_unsigned_to_nat(1u);
v___x_1883_ = lean_nat_sub(v_x_1823_, v___x_1882_);
lean_dec(v_x_1823_);
v_x_1821_ = v_fn_1879_;
v_x_1822_ = v___x_1881_;
v_x_1823_ = v___x_1883_;
goto _start;
}
else
{
lean_dec(v_x_1823_);
if (v_skipConstInApp_1820_ == 0)
{
goto v___jp_1876_;
}
else
{
uint8_t v___x_1885_; 
v___x_1885_ = l_Lean_Expr_isConst(v_x_1821_);
if (v___x_1885_ == 0)
{
goto v___jp_1876_;
}
else
{
v_f_1831_ = v_x_1821_;
v___y_1832_ = v___y_1824_;
v___y_1833_ = v___y_1825_;
v___y_1834_ = v___y_1826_;
v___y_1835_ = v___y_1827_;
v___y_1836_ = v___y_1828_;
goto v___jp_1830_;
}
}
}
v___jp_1830_:
{
if (v_skipInstances_1816_ == 0)
{
size_t v_sz_1837_; size_t v___x_1838_; lean_object* v___x_1839_; 
v_sz_1837_ = lean_array_size(v_x_1822_);
v___x_1838_ = ((size_t)0ULL);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc_ref(v_post_1818_);
lean_inc_ref(v_pre_1817_);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1817_, v_post_1818_, v_usedLetOnly_1819_, v_skipConstInApp_1820_, v_skipInstances_1816_, v_sz_1837_, v___x_1838_, v_x_1822_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref(v___x_1839_);
v___x_1841_ = l_Lean_mkAppN(v_f_1831_, v_a_1840_);
lean_dec(v_a_1840_);
v___x_1842_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1817_, v_post_1818_, v_usedLetOnly_1819_, v_skipConstInApp_1820_, v_skipInstances_1816_, v___x_1841_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
return v___x_1842_;
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v_f_1831_);
lean_dec_ref(v_post_1818_);
lean_dec_ref(v_pre_1817_);
v_a_1843_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1839_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1839_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_array_get_size(v_x_1822_);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc_ref(v_f_1831_);
v___x_1852_ = l_Lean_Meta_getFunInfoNArgs(v_f_1831_, v___x_1851_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v_paramInfo_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref(v___x_1852_);
v_paramInfo_1854_ = lean_ctor_get(v_a_1853_, 0);
lean_inc_ref(v_paramInfo_1854_);
lean_dec(v_a_1853_);
v___x_1855_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc_ref(v_post_1818_);
lean_inc_ref(v_pre_1817_);
v___x_1856_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1851_, v_paramInfo_1854_, v_pre_1817_, v_post_1818_, v_usedLetOnly_1819_, v_skipConstInApp_1820_, v_skipInstances_1816_, v___x_1855_, v_x_1822_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec_ref(v_paramInfo_1854_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref(v___x_1856_);
v___x_1858_ = l_Lean_mkAppN(v_f_1831_, v_a_1857_);
lean_dec(v_a_1857_);
v___x_1859_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1817_, v_post_1818_, v_usedLetOnly_1819_, v_skipConstInApp_1820_, v_skipInstances_1816_, v___x_1858_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
return v___x_1859_;
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v_f_1831_);
lean_dec_ref(v_post_1818_);
lean_dec_ref(v_pre_1817_);
v_a_1860_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1856_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1856_);
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
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
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
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v_f_1831_);
lean_dec_ref(v_x_1822_);
lean_dec_ref(v_post_1818_);
lean_dec_ref(v_pre_1817_);
v_a_1868_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1852_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1852_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
v___jp_1876_:
{
lean_object* v___x_1877_; 
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc_ref(v_post_1818_);
lean_inc_ref(v_pre_1817_);
v___x_1877_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1817_, v_post_1818_, v_usedLetOnly_1819_, v_skipConstInApp_1820_, v_skipInstances_1816_, v_x_1821_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref(v___x_1877_);
v_f_1831_ = v_a_1878_;
v___y_1832_ = v___y_1824_;
v___y_1833_ = v___y_1825_;
v___y_1834_ = v___y_1826_;
v___y_1835_ = v___y_1827_;
v___y_1836_ = v___y_1828_;
goto v___jp_1830_;
}
else
{
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v_x_1822_);
lean_dec_ref(v_post_1818_);
lean_dec_ref(v_pre_1817_);
return v___x_1877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v_pre_1886_, lean_object* v_e_1887_, lean_object* v_post_1888_, uint8_t v_usedLetOnly_1889_, uint8_t v_skipConstInApp_1890_, uint8_t v_skipInstances_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; 
lean_inc_ref(v_pre_1886_);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
lean_inc(v___y_1894_);
lean_inc_ref(v___y_1893_);
lean_inc_ref(v_e_1887_);
v___x_1898_ = lean_apply_6(v_pre_1886_, v_e_1887_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, lean_box(0));
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1947_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1947_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1947_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___y_1904_; 
switch(lean_obj_tag(v_a_1899_))
{
case 0:
{
lean_object* v_e_1939_; lean_object* v___x_1941_; 
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v_post_1888_);
lean_dec_ref(v_e_1887_);
lean_dec_ref(v_pre_1886_);
v_e_1939_ = lean_ctor_get(v_a_1899_, 0);
lean_inc_ref(v_e_1939_);
lean_dec_ref(v_a_1899_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v_e_1939_);
v___x_1941_ = v___x_1901_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_e_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
case 1:
{
lean_object* v_e_1943_; lean_object* v___x_1944_; 
lean_del_object(v___x_1901_);
lean_dec_ref(v_e_1887_);
v_e_1943_ = lean_ctor_get(v_a_1899_, 0);
lean_inc_ref(v_e_1943_);
lean_dec_ref(v_a_1899_);
v___x_1944_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1886_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v_e_1943_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v___x_1944_;
}
default: 
{
lean_object* v_e_x3f_1945_; 
lean_del_object(v___x_1901_);
v_e_x3f_1945_ = lean_ctor_get(v_a_1899_, 0);
lean_inc(v_e_x3f_1945_);
lean_dec_ref(v_a_1899_);
if (lean_obj_tag(v_e_x3f_1945_) == 0)
{
v___y_1904_ = v_e_1887_;
goto v___jp_1903_;
}
else
{
lean_object* v_val_1946_; 
lean_dec_ref(v_e_1887_);
v_val_1946_ = lean_ctor_get(v_e_x3f_1945_, 0);
lean_inc(v_val_1946_);
lean_dec_ref(v_e_x3f_1945_);
v___y_1904_ = v_val_1946_;
goto v___jp_1903_;
}
}
}
v___jp_1903_:
{
switch(lean_obj_tag(v___y_1904_))
{
case 7:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1906_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1886_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v___x_1905_, v___y_1904_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v___x_1906_;
}
case 6:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1908_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1886_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v___x_1907_, v___y_1904_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v___x_1908_;
}
case 8:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1910_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1886_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v___x_1909_, v___y_1904_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v___x_1910_;
}
case 5:
{
lean_object* v_dummy_1911_; lean_object* v_nargs_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_dummy_1911_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_1912_ = l_Lean_Expr_getAppNumArgs(v___y_1904_);
lean_inc(v_nargs_1912_);
v___x_1913_ = lean_mk_array(v_nargs_1912_, v_dummy_1911_);
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_nat_sub(v_nargs_1912_, v___x_1914_);
lean_dec(v_nargs_1912_);
v___x_1916_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1891_, v_pre_1886_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v___y_1904_, v___x_1913_, v___x_1915_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v___x_1916_;
}
case 10:
{
lean_object* v_data_1917_; lean_object* v_expr_1918_; lean_object* v___x_1919_; 
v_data_1917_ = lean_ctor_get(v___y_1904_, 0);
v_expr_1918_ = lean_ctor_get(v___y_1904_, 1);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
lean_inc(v___y_1894_);
lean_inc_ref(v___y_1893_);
lean_inc(v___y_1892_);
lean_inc_ref(v_expr_1918_);
lean_inc_ref(v_post_1888_);
lean_inc_ref(v_pre_1886_);
v___x_1919_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1886_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v_expr_1918_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; size_t v___x_1921_; size_t v___x_1922_; uint8_t v___x_1923_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref(v___x_1919_);
v___x_1921_ = lean_ptr_addr(v_expr_1918_);
v___x_1922_ = lean_ptr_addr(v_a_1920_);
v___x_1923_ = lean_usize_dec_eq(v___x_1921_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_inc(v_data_1917_);
lean_dec_ref(v___y_1904_);
v___x_1924_ = l_Lean_Expr_mdata___override(v_data_1917_, v_a_1920_);
v___x_1925_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1886_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v___x_1924_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; 
lean_dec(v_a_1920_);
v___x_1926_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1886_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v___y_1904_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v___x_1926_;
}
}
else
{
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v_post_1888_);
lean_dec_ref(v_pre_1886_);
return v___x_1919_;
}
}
case 11:
{
lean_object* v_typeName_1927_; lean_object* v_idx_1928_; lean_object* v_struct_1929_; lean_object* v___x_1930_; 
v_typeName_1927_ = lean_ctor_get(v___y_1904_, 0);
v_idx_1928_ = lean_ctor_get(v___y_1904_, 1);
v_struct_1929_ = lean_ctor_get(v___y_1904_, 2);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
lean_inc(v___y_1894_);
lean_inc_ref(v___y_1893_);
lean_inc(v___y_1892_);
lean_inc_ref(v_struct_1929_);
lean_inc_ref(v_post_1888_);
lean_inc_ref(v_pre_1886_);
v___x_1930_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1886_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v_struct_1929_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; size_t v___x_1932_; size_t v___x_1933_; uint8_t v___x_1934_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref(v___x_1930_);
v___x_1932_ = lean_ptr_addr(v_struct_1929_);
v___x_1933_ = lean_ptr_addr(v_a_1931_);
v___x_1934_ = lean_usize_dec_eq(v___x_1932_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
lean_inc(v_idx_1928_);
lean_inc(v_typeName_1927_);
lean_dec_ref(v___y_1904_);
v___x_1935_ = l_Lean_Expr_proj___override(v_typeName_1927_, v_idx_1928_, v_a_1931_);
v___x_1936_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1886_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v___x_1935_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v___x_1936_;
}
else
{
lean_object* v___x_1937_; 
lean_dec(v_a_1931_);
v___x_1937_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1886_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v___y_1904_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v___x_1937_;
}
}
else
{
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v_post_1888_);
lean_dec_ref(v_pre_1886_);
return v___x_1930_;
}
}
default: 
{
lean_object* v___x_1938_; 
v___x_1938_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1886_, v_post_1888_, v_usedLetOnly_1889_, v_skipConstInApp_1890_, v_skipInstances_1891_, v___y_1904_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
return v___x_1938_;
}
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v_post_1888_);
lean_dec_ref(v_e_1887_);
lean_dec_ref(v_pre_1886_);
v_a_1948_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1898_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1898_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v_pre_1956_, lean_object* v_e_1957_, lean_object* v_post_1958_, lean_object* v_usedLetOnly_1959_, lean_object* v_skipConstInApp_1960_, lean_object* v_skipInstances_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
uint8_t v_usedLetOnly_boxed_1968_; uint8_t v_skipConstInApp_boxed_1969_; uint8_t v_skipInstances_boxed_1970_; lean_object* v_res_1971_; 
v_usedLetOnly_boxed_1968_ = lean_unbox(v_usedLetOnly_1959_);
v_skipConstInApp_boxed_1969_ = lean_unbox(v_skipConstInApp_1960_);
v_skipInstances_boxed_1970_ = lean_unbox(v_skipInstances_1961_);
v_res_1971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v_pre_1956_, v_e_1957_, v_post_1958_, v_usedLetOnly_boxed_1968_, v_skipConstInApp_boxed_1969_, v_skipInstances_boxed_1970_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_1972_, lean_object* v_post_1973_, uint8_t v_usedLetOnly_1974_, uint8_t v_skipConstInApp_1975_, uint8_t v_skipInstances_1976_, lean_object* v_e_1977_, lean_object* v_a_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_inc(v_a_1978_);
v___x_1984_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1984_, 0, lean_box(0));
lean_closure_set(v___x_1984_, 1, lean_box(0));
lean_closure_set(v___x_1984_, 2, v_a_1978_);
v___x_1985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_1984_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2019_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_2019_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2019_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_1986_, v_e_1977_);
lean_dec(v_a_1986_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___f_1994_; lean_object* v___x_1995_; 
lean_del_object(v___x_1988_);
v___x_1991_ = lean_box(v_usedLetOnly_1974_);
v___x_1992_ = lean_box(v_skipConstInApp_1975_);
v___x_1993_ = lean_box(v_skipInstances_1976_);
lean_inc_ref(v_e_1977_);
v___f_1994_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1994_, 0, v_pre_1972_);
lean_closure_set(v___f_1994_, 1, v_e_1977_);
lean_closure_set(v___f_1994_, 2, v_post_1973_);
lean_closure_set(v___f_1994_, 3, v___x_1991_);
lean_closure_set(v___f_1994_, 4, v___x_1992_);
lean_closure_set(v___f_1994_, 5, v___x_1993_);
lean_inc(v___y_1982_);
lean_inc_ref(v___y_1981_);
lean_inc(v___y_1980_);
lean_inc_ref(v___y_1979_);
lean_inc(v_a_1978_);
v___x_1995_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_1994_, v_a_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref(v___x_1995_);
lean_inc(v_a_1996_);
v___f_1997_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1997_, 0, v_a_1978_);
lean_closure_set(v___f_1997_, 1, v_e_1977_);
lean_closure_set(v___f_1997_, 2, v_a_1996_);
v___x_1998_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_1997_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v___x_1998_, 0);
lean_dec(v_unused_2006_);
v___x_2000_ = v___x_1998_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_dec(v___x_1998_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v_a_1996_);
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1996_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v_a_1996_);
v_a_2007_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1998_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1998_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_e_1977_);
return v___x_1995_;
}
}
else
{
lean_object* v_val_2015_; lean_object* v___x_2017_; 
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_e_1977_);
lean_dec_ref(v_post_1973_);
lean_dec_ref(v_pre_1972_);
v_val_2015_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_val_2015_);
lean_dec_ref(v___x_1990_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v_val_2015_);
v___x_2017_ = v___x_1988_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_val_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_e_1977_);
lean_dec_ref(v_post_1973_);
lean_dec_ref(v_pre_1972_);
v_a_2020_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1985_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1985_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_2028_, lean_object* v_pre_2029_, lean_object* v_post_2030_, lean_object* v_usedLetOnly_2031_, lean_object* v_skipConstInApp_2032_, lean_object* v_skipInstances_2033_, lean_object* v_body_2034_, lean_object* v_x_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
uint8_t v_usedLetOnly_boxed_2042_; uint8_t v_skipConstInApp_boxed_2043_; uint8_t v_skipInstances_boxed_2044_; lean_object* v_res_2045_; 
v_usedLetOnly_boxed_2042_ = lean_unbox(v_usedLetOnly_2031_);
v_skipConstInApp_boxed_2043_ = lean_unbox(v_skipConstInApp_2032_);
v_skipInstances_boxed_2044_ = lean_unbox(v_skipInstances_2033_);
v_res_2045_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_2028_, v_pre_2029_, v_post_2030_, v_usedLetOnly_boxed_2042_, v_skipConstInApp_boxed_2043_, v_skipInstances_boxed_2044_, v_body_2034_, v_x_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2046_, lean_object* v_post_2047_, uint8_t v_usedLetOnly_2048_, uint8_t v_skipConstInApp_2049_, uint8_t v_skipInstances_2050_, lean_object* v_fvars_2051_, lean_object* v_e_2052_, lean_object* v_a_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
if (lean_obj_tag(v_e_2052_) == 7)
{
lean_object* v_binderName_2059_; lean_object* v_binderType_2060_; lean_object* v_body_2061_; uint8_t v_binderInfo_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v_binderName_2059_ = lean_ctor_get(v_e_2052_, 0);
lean_inc(v_binderName_2059_);
v_binderType_2060_ = lean_ctor_get(v_e_2052_, 1);
lean_inc_ref(v_binderType_2060_);
v_body_2061_ = lean_ctor_get(v_e_2052_, 2);
lean_inc_ref(v_body_2061_);
v_binderInfo_2062_ = lean_ctor_get_uint8(v_e_2052_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2052_);
v___x_2063_ = lean_expr_instantiate_rev(v_binderType_2060_, v_fvars_2051_);
lean_dec_ref(v_binderType_2060_);
lean_inc(v___y_2057_);
lean_inc_ref(v___y_2056_);
lean_inc(v___y_2055_);
lean_inc_ref(v___y_2054_);
lean_inc(v_a_2053_);
lean_inc_ref(v_post_2047_);
lean_inc_ref(v_pre_2046_);
v___x_2064_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2046_, v_post_2047_, v_usedLetOnly_2048_, v_skipConstInApp_2049_, v_skipInstances_2050_, v___x_2063_, v_a_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___f_2069_; uint8_t v___x_2070_; lean_object* v___x_2071_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref(v___x_2064_);
v___x_2066_ = lean_box(v_usedLetOnly_2048_);
v___x_2067_ = lean_box(v_skipConstInApp_2049_);
v___x_2068_ = lean_box(v_skipInstances_2050_);
v___f_2069_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2069_, 0, v_fvars_2051_);
lean_closure_set(v___f_2069_, 1, v_pre_2046_);
lean_closure_set(v___f_2069_, 2, v_post_2047_);
lean_closure_set(v___f_2069_, 3, v___x_2066_);
lean_closure_set(v___f_2069_, 4, v___x_2067_);
lean_closure_set(v___f_2069_, 5, v___x_2068_);
lean_closure_set(v___f_2069_, 6, v_body_2061_);
v___x_2070_ = 0;
v___x_2071_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2059_, v_binderInfo_2062_, v_a_2065_, v___f_2069_, v___x_2070_, v_a_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
return v___x_2071_;
}
else
{
lean_dec_ref(v_body_2061_);
lean_dec(v_binderName_2059_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_fvars_2051_);
lean_dec_ref(v_post_2047_);
lean_dec_ref(v_pre_2046_);
return v___x_2064_;
}
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_expr_instantiate_rev(v_e_2052_, v_fvars_2051_);
lean_dec_ref(v_e_2052_);
lean_inc(v___y_2057_);
lean_inc_ref(v___y_2056_);
lean_inc(v___y_2055_);
lean_inc_ref(v___y_2054_);
lean_inc(v_a_2053_);
lean_inc_ref(v_post_2047_);
lean_inc_ref(v_pre_2046_);
v___x_2073_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2046_, v_post_2047_, v_usedLetOnly_2048_, v_skipConstInApp_2049_, v_skipInstances_2050_, v___x_2072_, v_a_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; uint8_t v___x_2075_; uint8_t v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_2073_);
v___x_2075_ = 0;
v___x_2076_ = 1;
v___x_2077_ = 1;
v___x_2078_ = l_Lean_Meta_mkForallFVars(v_fvars_2051_, v_a_2074_, v___x_2075_, v_usedLetOnly_2048_, v___x_2076_, v___x_2077_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec_ref(v_fvars_2051_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2080_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref(v___x_2078_);
v___x_2080_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2046_, v_post_2047_, v_usedLetOnly_2048_, v_skipConstInApp_2049_, v_skipInstances_2050_, v_a_2079_, v_a_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
return v___x_2080_;
}
else
{
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_post_2047_);
lean_dec_ref(v_pre_2046_);
return v___x_2078_;
}
}
else
{
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_fvars_2051_);
lean_dec_ref(v_post_2047_);
lean_dec_ref(v_pre_2046_);
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2081_, lean_object* v_pre_2082_, lean_object* v_post_2083_, uint8_t v_usedLetOnly_2084_, uint8_t v_skipConstInApp_2085_, uint8_t v_skipInstances_2086_, lean_object* v_body_2087_, lean_object* v_x_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = lean_array_push(v_fvars_2081_, v_x_2088_);
v___x_2096_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2082_, v_post_2083_, v_usedLetOnly_2084_, v_skipConstInApp_2085_, v_skipInstances_2086_, v___x_2095_, v_body_2087_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2097_, lean_object* v_post_2098_, lean_object* v_usedLetOnly_2099_, lean_object* v_skipConstInApp_2100_, lean_object* v_skipInstances_2101_, lean_object* v_e_2102_, lean_object* v_a_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
uint8_t v_usedLetOnly_boxed_2109_; uint8_t v_skipConstInApp_boxed_2110_; uint8_t v_skipInstances_boxed_2111_; lean_object* v_res_2112_; 
v_usedLetOnly_boxed_2109_ = lean_unbox(v_usedLetOnly_2099_);
v_skipConstInApp_boxed_2110_ = lean_unbox(v_skipConstInApp_2100_);
v_skipInstances_boxed_2111_ = lean_unbox(v_skipInstances_2101_);
v_res_2112_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2097_, v_post_2098_, v_usedLetOnly_boxed_2109_, v_skipConstInApp_boxed_2110_, v_skipInstances_boxed_2111_, v_e_2102_, v_a_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_pre_2113_, lean_object* v_post_2114_, lean_object* v_usedLetOnly_2115_, lean_object* v_skipConstInApp_2116_, lean_object* v_skipInstances_2117_, lean_object* v_sz_2118_, lean_object* v_i_2119_, lean_object* v_bs_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
uint8_t v_usedLetOnly_boxed_2127_; uint8_t v_skipConstInApp_boxed_2128_; uint8_t v_skipInstances_boxed_2129_; size_t v_sz_boxed_2130_; size_t v_i_boxed_2131_; lean_object* v_res_2132_; 
v_usedLetOnly_boxed_2127_ = lean_unbox(v_usedLetOnly_2115_);
v_skipConstInApp_boxed_2128_ = lean_unbox(v_skipConstInApp_2116_);
v_skipInstances_boxed_2129_ = lean_unbox(v_skipInstances_2117_);
v_sz_boxed_2130_ = lean_unbox_usize(v_sz_2118_);
lean_dec(v_sz_2118_);
v_i_boxed_2131_ = lean_unbox_usize(v_i_2119_);
lean_dec(v_i_2119_);
v_res_2132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_2113_, v_post_2114_, v_usedLetOnly_boxed_2127_, v_skipConstInApp_boxed_2128_, v_skipInstances_boxed_2129_, v_sz_boxed_2130_, v_i_boxed_2131_, v_bs_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2133_, lean_object* v_post_2134_, lean_object* v_usedLetOnly_2135_, lean_object* v_skipConstInApp_2136_, lean_object* v_skipInstances_2137_, lean_object* v_e_2138_, lean_object* v_a_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
uint8_t v_usedLetOnly_boxed_2145_; uint8_t v_skipConstInApp_boxed_2146_; uint8_t v_skipInstances_boxed_2147_; lean_object* v_res_2148_; 
v_usedLetOnly_boxed_2145_ = lean_unbox(v_usedLetOnly_2135_);
v_skipConstInApp_boxed_2146_ = lean_unbox(v_skipConstInApp_2136_);
v_skipInstances_boxed_2147_ = lean_unbox(v_skipInstances_2137_);
v_res_2148_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2133_, v_post_2134_, v_usedLetOnly_boxed_2145_, v_skipConstInApp_boxed_2146_, v_skipInstances_boxed_2147_, v_e_2138_, v_a_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2149_, lean_object* v_post_2150_, lean_object* v_usedLetOnly_2151_, lean_object* v_skipConstInApp_2152_, lean_object* v_skipInstances_2153_, lean_object* v_fvars_2154_, lean_object* v_e_2155_, lean_object* v_a_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
uint8_t v_usedLetOnly_boxed_2162_; uint8_t v_skipConstInApp_boxed_2163_; uint8_t v_skipInstances_boxed_2164_; lean_object* v_res_2165_; 
v_usedLetOnly_boxed_2162_ = lean_unbox(v_usedLetOnly_2151_);
v_skipConstInApp_boxed_2163_ = lean_unbox(v_skipConstInApp_2152_);
v_skipInstances_boxed_2164_ = lean_unbox(v_skipInstances_2153_);
v_res_2165_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2149_, v_post_2150_, v_usedLetOnly_boxed_2162_, v_skipConstInApp_boxed_2163_, v_skipInstances_boxed_2164_, v_fvars_2154_, v_e_2155_, v_a_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2166_, lean_object* v_post_2167_, lean_object* v_usedLetOnly_2168_, lean_object* v_skipConstInApp_2169_, lean_object* v_skipInstances_2170_, lean_object* v_fvars_2171_, lean_object* v_e_2172_, lean_object* v_a_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
uint8_t v_usedLetOnly_boxed_2179_; uint8_t v_skipConstInApp_boxed_2180_; uint8_t v_skipInstances_boxed_2181_; lean_object* v_res_2182_; 
v_usedLetOnly_boxed_2179_ = lean_unbox(v_usedLetOnly_2168_);
v_skipConstInApp_boxed_2180_ = lean_unbox(v_skipConstInApp_2169_);
v_skipInstances_boxed_2181_ = lean_unbox(v_skipInstances_2170_);
v_res_2182_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2166_, v_post_2167_, v_usedLetOnly_boxed_2179_, v_skipConstInApp_boxed_2180_, v_skipInstances_boxed_2181_, v_fvars_2171_, v_e_2172_, v_a_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2183_, lean_object* v_post_2184_, lean_object* v_usedLetOnly_2185_, lean_object* v_skipConstInApp_2186_, lean_object* v_skipInstances_2187_, lean_object* v_fvars_2188_, lean_object* v_e_2189_, lean_object* v_a_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
uint8_t v_usedLetOnly_boxed_2196_; uint8_t v_skipConstInApp_boxed_2197_; uint8_t v_skipInstances_boxed_2198_; lean_object* v_res_2199_; 
v_usedLetOnly_boxed_2196_ = lean_unbox(v_usedLetOnly_2185_);
v_skipConstInApp_boxed_2197_ = lean_unbox(v_skipConstInApp_2186_);
v_skipInstances_boxed_2198_ = lean_unbox(v_skipInstances_2187_);
v_res_2199_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2183_, v_post_2184_, v_usedLetOnly_boxed_2196_, v_skipConstInApp_boxed_2197_, v_skipInstances_boxed_2198_, v_fvars_2188_, v_e_2189_, v_a_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object* v_upperBound_2200_, lean_object* v___x_2201_, lean_object* v_pre_2202_, lean_object* v_post_2203_, lean_object* v_usedLetOnly_2204_, lean_object* v_skipConstInApp_2205_, lean_object* v_skipInstances_2206_, lean_object* v_a_2207_, lean_object* v_b_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
uint8_t v_usedLetOnly_boxed_2215_; uint8_t v_skipConstInApp_boxed_2216_; uint8_t v_skipInstances_boxed_2217_; lean_object* v_res_2218_; 
v_usedLetOnly_boxed_2215_ = lean_unbox(v_usedLetOnly_2204_);
v_skipConstInApp_boxed_2216_ = lean_unbox(v_skipConstInApp_2205_);
v_skipInstances_boxed_2217_ = lean_unbox(v_skipInstances_2206_);
v_res_2218_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_2200_, v___x_2201_, v_pre_2202_, v_post_2203_, v_usedLetOnly_boxed_2215_, v_skipConstInApp_boxed_2216_, v_skipInstances_boxed_2217_, v_a_2207_, v_b_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec_ref(v___x_2201_);
lean_dec(v_upperBound_2200_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2219_, lean_object* v_pre_2220_, lean_object* v_post_2221_, lean_object* v_usedLetOnly_2222_, lean_object* v_skipConstInApp_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v_skipInstances_boxed_2233_; uint8_t v_usedLetOnly_boxed_2234_; uint8_t v_skipConstInApp_boxed_2235_; lean_object* v_res_2236_; 
v_skipInstances_boxed_2233_ = lean_unbox(v_skipInstances_2219_);
v_usedLetOnly_boxed_2234_ = lean_unbox(v_usedLetOnly_2222_);
v_skipConstInApp_boxed_2235_ = lean_unbox(v_skipConstInApp_2223_);
v_res_2236_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2233_, v_pre_2220_, v_post_2221_, v_usedLetOnly_boxed_2234_, v_skipConstInApp_boxed_2235_, v_x_2224_, v_x_2225_, v_x_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
return v_res_2236_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2238_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2238_, 0, lean_box(0));
lean_closure_set(v___x_2238_, 1, lean_box(0));
lean_closure_set(v___x_2238_, 2, v___x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2239_, lean_object* v_pre_2240_, lean_object* v_post_2241_, uint8_t v_usedLetOnly_2242_, uint8_t v_skipConstInApp_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v_a_2251_; uint8_t v___x_2252_; lean_object* v___x_2253_; 
v___x_2249_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2250_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2249_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2251_);
lean_dec_ref(v___x_2250_);
v___x_2252_ = 0;
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
lean_inc(v_a_2251_);
v___x_2253_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2240_, v_post_2241_, v_usedLetOnly_2242_, v_skipConstInApp_2243_, v___x_2252_, v_input_2239_, v_a_2251_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref(v___x_2253_);
v___x_2255_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2255_, 0, lean_box(0));
lean_closure_set(v___x_2255_, 1, lean_box(0));
lean_closure_set(v___x_2255_, 2, v_a_2251_);
v___x_2256_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2255_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2263_ == 0)
{
lean_object* v_unused_2264_; 
v_unused_2264_ = lean_ctor_get(v___x_2256_, 0);
lean_dec(v_unused_2264_);
v___x_2258_ = v___x_2256_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_dec(v___x_2256_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v_a_2254_);
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2254_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
else
{
lean_dec(v_a_2251_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v___x_2253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2265_, lean_object* v_pre_2266_, lean_object* v_post_2267_, lean_object* v_usedLetOnly_2268_, lean_object* v_skipConstInApp_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
uint8_t v_usedLetOnly_boxed_2275_; uint8_t v_skipConstInApp_boxed_2276_; lean_object* v_res_2277_; 
v_usedLetOnly_boxed_2275_ = lean_unbox(v_usedLetOnly_2268_);
v_skipConstInApp_boxed_2276_ = lean_unbox(v_skipConstInApp_2269_);
v_res_2277_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2265_, v_pre_2266_, v_post_2267_, v_usedLetOnly_boxed_2275_, v_skipConstInApp_boxed_2276_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_st_ref_get(v_val_2278_);
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object* v_val_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v_val_2286_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2293_, lean_object* v_val_2294_, lean_object* v_a_2295_, lean_object* v___x_2296_, lean_object* v_____r_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2303_ = lean_st_ref_take(v_val_2293_);
v___x_2304_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2294_, v_a_2295_, v___x_2303_);
v___x_2305_ = lean_st_ref_set(v_val_2293_, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2296_);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2308_, lean_object* v_val_2309_, lean_object* v_a_2310_, lean_object* v___x_2311_, lean_object* v_____r_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2308_, v_val_2309_, v_a_2310_, v___x_2311_, v_____r_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v_val_2309_);
lean_dec(v_val_2308_);
return v_res_2318_;
}
}
static uint64_t _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0(void){
_start:
{
uint8_t v___x_2319_; uint64_t v___x_2320_; 
v___x_2319_ = 2;
v___x_2320_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_upperBound_2321_, lean_object* v_val_2322_, lean_object* v_next_2323_, lean_object* v_params_2324_, lean_object* v___x_2325_, lean_object* v_val_2326_, lean_object* v_next_2327_, uint8_t v___x_2328_, lean_object* v_a_2329_, uint8_t v_b_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
uint8_t v_a_2337_; uint8_t v___x_2341_; 
v___x_2341_ = lean_nat_dec_lt(v_a_2329_, v_upperBound_2321_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec(v_a_2329_);
lean_dec(v_next_2327_);
lean_dec_ref(v___x_2325_);
v___x_2342_ = lean_box(v_b_2330_);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
else
{
lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2344_ = lean_st_ref_get(v_val_2322_);
v___x_2345_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2323_, v_a_2329_, v___x_2344_);
lean_dec(v___x_2344_);
if (v___x_2345_ == 0)
{
v_a_2337_ = v_b_2330_;
goto v___jp_2336_;
}
else
{
lean_object* v___x_2346_; uint8_t v_foApprox_2347_; uint8_t v_ctxApprox_2348_; uint8_t v_quasiPatternApprox_2349_; uint8_t v_constApprox_2350_; uint8_t v_isDefEqStuckEx_2351_; uint8_t v_unificationHints_2352_; uint8_t v_assignSyntheticOpaque_2353_; uint8_t v_offsetCnstrs_2354_; uint8_t v_transparency_2355_; uint8_t v_etaStruct_2356_; uint8_t v_univApprox_2357_; uint8_t v_iota_2358_; uint8_t v_beta_2359_; uint8_t v_proj_2360_; uint8_t v_zeta_2361_; uint8_t v_zetaDelta_2362_; uint8_t v_zetaUnused_2363_; uint8_t v_zetaHave_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2427_; 
v___x_2346_ = l_Lean_Meta_Context_config(v___y_2331_);
v_foApprox_2347_ = lean_ctor_get_uint8(v___x_2346_, 0);
v_ctxApprox_2348_ = lean_ctor_get_uint8(v___x_2346_, 1);
v_quasiPatternApprox_2349_ = lean_ctor_get_uint8(v___x_2346_, 2);
v_constApprox_2350_ = lean_ctor_get_uint8(v___x_2346_, 3);
v_isDefEqStuckEx_2351_ = lean_ctor_get_uint8(v___x_2346_, 4);
v_unificationHints_2352_ = lean_ctor_get_uint8(v___x_2346_, 5);
v_assignSyntheticOpaque_2353_ = lean_ctor_get_uint8(v___x_2346_, 7);
v_offsetCnstrs_2354_ = lean_ctor_get_uint8(v___x_2346_, 8);
v_transparency_2355_ = lean_ctor_get_uint8(v___x_2346_, 9);
v_etaStruct_2356_ = lean_ctor_get_uint8(v___x_2346_, 10);
v_univApprox_2357_ = lean_ctor_get_uint8(v___x_2346_, 11);
v_iota_2358_ = lean_ctor_get_uint8(v___x_2346_, 12);
v_beta_2359_ = lean_ctor_get_uint8(v___x_2346_, 13);
v_proj_2360_ = lean_ctor_get_uint8(v___x_2346_, 14);
v_zeta_2361_ = lean_ctor_get_uint8(v___x_2346_, 15);
v_zetaDelta_2362_ = lean_ctor_get_uint8(v___x_2346_, 16);
v_zetaUnused_2363_ = lean_ctor_get_uint8(v___x_2346_, 17);
v_zetaHave_2364_ = lean_ctor_get_uint8(v___x_2346_, 18);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2366_ = v___x_2346_;
v_isShared_2367_ = v_isSharedCheck_2427_;
goto v_resetjp_2365_;
}
else
{
lean_dec(v___x_2346_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2427_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
uint8_t v_trackZetaDelta_2368_; lean_object* v_zetaDeltaSet_2369_; lean_object* v_lctx_2370_; lean_object* v_localInstances_2371_; lean_object* v_defEqCtx_x3f_2372_; lean_object* v_synthPendingDepth_2373_; lean_object* v_canUnfold_x3f_2374_; uint8_t v_univApprox_2375_; uint8_t v_inTypeClassResolution_2376_; uint8_t v_cacheInferType_2377_; uint8_t v___x_2378_; lean_object* v___x_2380_; 
v_trackZetaDelta_2368_ = lean_ctor_get_uint8(v___y_2331_, sizeof(void*)*7);
v_zetaDeltaSet_2369_ = lean_ctor_get(v___y_2331_, 1);
v_lctx_2370_ = lean_ctor_get(v___y_2331_, 2);
v_localInstances_2371_ = lean_ctor_get(v___y_2331_, 3);
v_defEqCtx_x3f_2372_ = lean_ctor_get(v___y_2331_, 4);
v_synthPendingDepth_2373_ = lean_ctor_get(v___y_2331_, 5);
v_canUnfold_x3f_2374_ = lean_ctor_get(v___y_2331_, 6);
v_univApprox_2375_ = lean_ctor_get_uint8(v___y_2331_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2376_ = lean_ctor_get_uint8(v___y_2331_, sizeof(void*)*7 + 2);
v_cacheInferType_2377_ = lean_ctor_get_uint8(v___y_2331_, sizeof(void*)*7 + 3);
v___x_2378_ = 0;
if (v_isShared_2367_ == 0)
{
v___x_2380_ = v___x_2366_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 0, v_foApprox_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 1, v_ctxApprox_2348_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 2, v_quasiPatternApprox_2349_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 3, v_constApprox_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 4, v_isDefEqStuckEx_2351_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 5, v_unificationHints_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 7, v_assignSyntheticOpaque_2353_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 8, v_offsetCnstrs_2354_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 9, v_transparency_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 10, v_etaStruct_2356_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 11, v_univApprox_2357_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 12, v_iota_2358_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 13, v_beta_2359_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 14, v_proj_2360_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 15, v_zeta_2361_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 16, v_zetaDelta_2362_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 17, v_zetaUnused_2363_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, 18, v_zetaHave_2364_);
v___x_2380_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
uint64_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v_foApprox_2385_; uint8_t v_ctxApprox_2386_; uint8_t v_quasiPatternApprox_2387_; uint8_t v_constApprox_2388_; uint8_t v_isDefEqStuckEx_2389_; uint8_t v_unificationHints_2390_; uint8_t v_proofIrrelevance_2391_; uint8_t v_assignSyntheticOpaque_2392_; uint8_t v_offsetCnstrs_2393_; uint8_t v_etaStruct_2394_; uint8_t v_univApprox_2395_; uint8_t v_iota_2396_; uint8_t v_beta_2397_; uint8_t v_proj_2398_; uint8_t v_zeta_2399_; uint8_t v_zetaDelta_2400_; uint8_t v_zetaUnused_2401_; uint8_t v_zetaHave_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2425_; 
lean_ctor_set_uint8(v___x_2380_, 6, v___x_2378_);
v___x_2381_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2380_);
v___x_2382_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2382_, 0, v___x_2380_);
lean_ctor_set_uint64(v___x_2382_, sizeof(void*)*1, v___x_2381_);
lean_inc(v_canUnfold_x3f_2374_);
lean_inc(v_synthPendingDepth_2373_);
lean_inc(v_defEqCtx_x3f_2372_);
lean_inc_ref(v_localInstances_2371_);
lean_inc_ref(v_lctx_2370_);
lean_inc(v_zetaDeltaSet_2369_);
v___x_2383_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set(v___x_2383_, 1, v_zetaDeltaSet_2369_);
lean_ctor_set(v___x_2383_, 2, v_lctx_2370_);
lean_ctor_set(v___x_2383_, 3, v_localInstances_2371_);
lean_ctor_set(v___x_2383_, 4, v_defEqCtx_x3f_2372_);
lean_ctor_set(v___x_2383_, 5, v_synthPendingDepth_2373_);
lean_ctor_set(v___x_2383_, 6, v_canUnfold_x3f_2374_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*7, v_trackZetaDelta_2368_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*7 + 1, v_univApprox_2375_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2376_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*7 + 3, v_cacheInferType_2377_);
v___x_2384_ = l_Lean_Meta_Context_config(v___x_2383_);
v_foApprox_2385_ = lean_ctor_get_uint8(v___x_2384_, 0);
v_ctxApprox_2386_ = lean_ctor_get_uint8(v___x_2384_, 1);
v_quasiPatternApprox_2387_ = lean_ctor_get_uint8(v___x_2384_, 2);
v_constApprox_2388_ = lean_ctor_get_uint8(v___x_2384_, 3);
v_isDefEqStuckEx_2389_ = lean_ctor_get_uint8(v___x_2384_, 4);
v_unificationHints_2390_ = lean_ctor_get_uint8(v___x_2384_, 5);
v_proofIrrelevance_2391_ = lean_ctor_get_uint8(v___x_2384_, 6);
v_assignSyntheticOpaque_2392_ = lean_ctor_get_uint8(v___x_2384_, 7);
v_offsetCnstrs_2393_ = lean_ctor_get_uint8(v___x_2384_, 8);
v_etaStruct_2394_ = lean_ctor_get_uint8(v___x_2384_, 10);
v_univApprox_2395_ = lean_ctor_get_uint8(v___x_2384_, 11);
v_iota_2396_ = lean_ctor_get_uint8(v___x_2384_, 12);
v_beta_2397_ = lean_ctor_get_uint8(v___x_2384_, 13);
v_proj_2398_ = lean_ctor_get_uint8(v___x_2384_, 14);
v_zeta_2399_ = lean_ctor_get_uint8(v___x_2384_, 15);
v_zetaDelta_2400_ = lean_ctor_get_uint8(v___x_2384_, 16);
v_zetaUnused_2401_ = lean_ctor_get_uint8(v___x_2384_, 17);
v_zetaHave_2402_ = lean_ctor_get_uint8(v___x_2384_, 18);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2404_ = v___x_2384_;
v_isShared_2405_ = v_isSharedCheck_2425_;
goto v_resetjp_2403_;
}
else
{
lean_dec(v___x_2384_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2425_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; uint8_t v___x_2407_; lean_object* v_config_2409_; 
v___x_2406_ = lean_array_fget_borrowed(v_params_2324_, v_a_2329_);
v___x_2407_ = 2;
if (v_isShared_2405_ == 0)
{
v_config_2409_ = v___x_2404_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 0, v_foApprox_2385_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 1, v_ctxApprox_2386_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 2, v_quasiPatternApprox_2387_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 3, v_constApprox_2388_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 4, v_isDefEqStuckEx_2389_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 5, v_unificationHints_2390_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 6, v_proofIrrelevance_2391_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 7, v_assignSyntheticOpaque_2392_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 8, v_offsetCnstrs_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 10, v_etaStruct_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 11, v_univApprox_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 12, v_iota_2396_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 13, v_beta_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 14, v_proj_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 15, v_zeta_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 16, v_zetaDelta_2400_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 17, v_zetaUnused_2401_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, 18, v_zetaHave_2402_);
v_config_2409_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
uint64_t v___x_2410_; uint64_t v___x_2411_; uint64_t v___x_2412_; uint64_t v___x_2413_; uint64_t v___x_2414_; uint64_t v_key_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_ctor_set_uint8(v_config_2409_, 9, v___x_2407_);
v___x_2410_ = l_Lean_Meta_Context_configKey(v___x_2383_);
lean_dec_ref(v___x_2383_);
v___x_2411_ = 2ULL;
v___x_2412_ = lean_uint64_shift_right(v___x_2410_, v___x_2411_);
v___x_2413_ = lean_uint64_shift_left(v___x_2412_, v___x_2411_);
v___x_2414_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0);
v_key_2415_ = lean_uint64_lor(v___x_2413_, v___x_2414_);
v___x_2416_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2416_, 0, v_config_2409_);
lean_ctor_set_uint64(v___x_2416_, sizeof(void*)*1, v_key_2415_);
lean_inc(v_canUnfold_x3f_2374_);
lean_inc(v_synthPendingDepth_2373_);
lean_inc(v_defEqCtx_x3f_2372_);
lean_inc_ref(v_localInstances_2371_);
lean_inc_ref(v_lctx_2370_);
lean_inc(v_zetaDeltaSet_2369_);
v___x_2417_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
lean_ctor_set(v___x_2417_, 1, v_zetaDeltaSet_2369_);
lean_ctor_set(v___x_2417_, 2, v_lctx_2370_);
lean_ctor_set(v___x_2417_, 3, v_localInstances_2371_);
lean_ctor_set(v___x_2417_, 4, v_defEqCtx_x3f_2372_);
lean_ctor_set(v___x_2417_, 5, v_synthPendingDepth_2373_);
lean_ctor_set(v___x_2417_, 6, v_canUnfold_x3f_2374_);
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*7, v_trackZetaDelta_2368_);
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*7 + 1, v_univApprox_2375_);
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2376_);
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*7 + 3, v_cacheInferType_2377_);
lean_inc(v___y_2334_);
lean_inc_ref(v___y_2333_);
lean_inc(v___y_2332_);
lean_inc_ref(v___x_2325_);
lean_inc(v___x_2406_);
v___x_2418_ = l_Lean_Meta_isExprDefEq(v___x_2406_, v___x_2325_, v___x_2417_, v___y_2332_, v___y_2333_, v___y_2334_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; uint8_t v___x_2420_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref(v___x_2418_);
v___x_2420_ = lean_unbox(v_a_2419_);
lean_dec(v_a_2419_);
if (v___x_2420_ == 0)
{
v_a_2337_ = v_b_2330_;
goto v___jp_2336_;
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2421_ = lean_st_ref_take(v_val_2322_);
lean_inc(v_a_2329_);
lean_inc(v_next_2327_);
v___x_2422_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2326_, v_next_2327_, v_next_2323_, v_a_2329_, v___x_2421_);
v___x_2423_ = lean_st_ref_set(v_val_2322_, v___x_2422_);
v_a_2337_ = v___x_2328_;
goto v___jp_2336_;
}
}
else
{
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec(v_a_2329_);
lean_dec(v_next_2327_);
lean_dec_ref(v___x_2325_);
return v___x_2418_;
}
}
}
}
}
}
}
v___jp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_unsigned_to_nat(1u);
v___x_2339_ = lean_nat_add(v_a_2329_, v___x_2338_);
lean_dec(v_a_2329_);
v_a_2329_ = v___x_2339_;
v_b_2330_ = v_a_2337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_upperBound_2428_, lean_object* v_val_2429_, lean_object* v_next_2430_, lean_object* v_params_2431_, lean_object* v___x_2432_, lean_object* v_val_2433_, lean_object* v_next_2434_, lean_object* v___x_2435_, lean_object* v_a_2436_, lean_object* v_b_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
uint8_t v___x_42471__boxed_2443_; uint8_t v_b_boxed_2444_; lean_object* v_res_2445_; 
v___x_42471__boxed_2443_ = lean_unbox(v___x_2435_);
v_b_boxed_2444_ = lean_unbox(v_b_2437_);
v_res_2445_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_2428_, v_val_2429_, v_next_2430_, v_params_2431_, v___x_2432_, v_val_2433_, v_next_2434_, v___x_42471__boxed_2443_, v_a_2436_, v_b_boxed_2444_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec_ref(v___y_2438_);
lean_dec(v_val_2433_);
lean_dec_ref(v_params_2431_);
lean_dec(v_next_2430_);
lean_dec(v_val_2429_);
lean_dec(v_upperBound_2428_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3_spec__3(lean_object* v_msgData_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; lean_object* v_env_2453_; lean_object* v___x_2454_; lean_object* v_mctx_2455_; lean_object* v_lctx_2456_; lean_object* v_options_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2452_ = lean_st_ref_get(v___y_2450_);
v_env_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc_ref(v_env_2453_);
lean_dec(v___x_2452_);
v___x_2454_ = lean_st_ref_get(v___y_2448_);
v_mctx_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc_ref(v_mctx_2455_);
lean_dec(v___x_2454_);
v_lctx_2456_ = lean_ctor_get(v___y_2447_, 2);
v_options_2457_ = lean_ctor_get(v___y_2449_, 2);
lean_inc_ref(v_options_2457_);
lean_inc_ref(v_lctx_2456_);
v___x_2458_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2458_, 0, v_env_2453_);
lean_ctor_set(v___x_2458_, 1, v_mctx_2455_);
lean_ctor_set(v___x_2458_, 2, v_lctx_2456_);
lean_ctor_set(v___x_2458_, 3, v_options_2457_);
v___x_2459_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
lean_ctor_set(v___x_2459_, 1, v_msgData_2446_);
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3_spec__3___boxed(lean_object* v_msgData_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3_spec__3(v_msgData_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
return v_res_2467_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2468_; double v___x_2469_; 
v___x_2468_ = lean_unsigned_to_nat(0u);
v___x_2469_ = lean_float_of_nat(v___x_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v_cls_2473_, lean_object* v_msg_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_ref_2480_; lean_object* v___x_2481_; lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2526_; 
v_ref_2480_ = lean_ctor_get(v___y_2477_, 5);
v___x_2481_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3_spec__3(v_msg_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2526_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2526_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; lean_object* v_traceState_2487_; lean_object* v_env_2488_; lean_object* v_nextMacroScope_2489_; lean_object* v_ngen_2490_; lean_object* v_auxDeclNGen_2491_; lean_object* v_cache_2492_; lean_object* v_messages_2493_; lean_object* v_infoState_2494_; lean_object* v_snapshotTasks_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2525_; 
v___x_2486_ = lean_st_ref_take(v___y_2478_);
v_traceState_2487_ = lean_ctor_get(v___x_2486_, 4);
v_env_2488_ = lean_ctor_get(v___x_2486_, 0);
v_nextMacroScope_2489_ = lean_ctor_get(v___x_2486_, 1);
v_ngen_2490_ = lean_ctor_get(v___x_2486_, 2);
v_auxDeclNGen_2491_ = lean_ctor_get(v___x_2486_, 3);
v_cache_2492_ = lean_ctor_get(v___x_2486_, 5);
v_messages_2493_ = lean_ctor_get(v___x_2486_, 6);
v_infoState_2494_ = lean_ctor_get(v___x_2486_, 7);
v_snapshotTasks_2495_ = lean_ctor_get(v___x_2486_, 8);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2497_ = v___x_2486_;
v_isShared_2498_ = v_isSharedCheck_2525_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_snapshotTasks_2495_);
lean_inc(v_infoState_2494_);
lean_inc(v_messages_2493_);
lean_inc(v_cache_2492_);
lean_inc(v_traceState_2487_);
lean_inc(v_auxDeclNGen_2491_);
lean_inc(v_ngen_2490_);
lean_inc(v_nextMacroScope_2489_);
lean_inc(v_env_2488_);
lean_dec(v___x_2486_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2525_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
uint64_t v_tid_2499_; lean_object* v_traces_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2524_; 
v_tid_2499_ = lean_ctor_get_uint64(v_traceState_2487_, sizeof(void*)*1);
v_traces_2500_ = lean_ctor_get(v_traceState_2487_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_traceState_2487_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2502_ = v_traceState_2487_;
v_isShared_2503_ = v_isSharedCheck_2524_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_traces_2500_);
lean_dec(v_traceState_2487_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2524_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2504_; double v___x_2505_; uint8_t v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2504_ = lean_box(0);
v___x_2505_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__0);
v___x_2506_ = 0;
v___x_2507_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__1));
v___x_2508_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2508_, 0, v_cls_2473_);
lean_ctor_set(v___x_2508_, 1, v___x_2504_);
lean_ctor_set(v___x_2508_, 2, v___x_2507_);
lean_ctor_set_float(v___x_2508_, sizeof(void*)*3, v___x_2505_);
lean_ctor_set_float(v___x_2508_, sizeof(void*)*3 + 8, v___x_2505_);
lean_ctor_set_uint8(v___x_2508_, sizeof(void*)*3 + 16, v___x_2506_);
v___x_2509_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__2));
v___x_2510_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2508_);
lean_ctor_set(v___x_2510_, 1, v_a_2482_);
lean_ctor_set(v___x_2510_, 2, v___x_2509_);
lean_inc(v_ref_2480_);
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_ref_2480_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = l_Lean_PersistentArray_push___redArg(v_traces_2500_, v___x_2511_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2512_);
v___x_2514_ = v___x_2502_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2512_);
lean_ctor_set_uint64(v_reuseFailAlloc_2523_, sizeof(void*)*1, v_tid_2499_);
v___x_2514_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2516_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 4, v___x_2514_);
v___x_2516_ = v___x_2497_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_env_2488_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_nextMacroScope_2489_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_ngen_2490_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_auxDeclNGen_2491_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2522_, 5, v_cache_2492_);
lean_ctor_set(v_reuseFailAlloc_2522_, 6, v_messages_2493_);
lean_ctor_set(v_reuseFailAlloc_2522_, 7, v_infoState_2494_);
lean_ctor_set(v_reuseFailAlloc_2522_, 8, v_snapshotTasks_2495_);
v___x_2516_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2517_ = lean_st_ref_set(v___y_2478_, v___x_2516_);
v___x_2518_ = lean_box(0);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v___x_2518_);
v___x_2520_ = v___x_2484_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v_cls_2527_, lean_object* v_msg_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(v_cls_2527_, v_msg_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
return v_res_2534_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__4));
v___x_2544_ = l_Lean_stringToMessageData(v___x_2543_);
return v___x_2544_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2546_ = l_Lean_stringToMessageData(v___x_2545_);
return v___x_2546_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9));
v___x_2552_ = l_Lean_stringToMessageData(v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13));
v___x_2558_ = l_Lean_stringToMessageData(v___x_2557_);
return v___x_2558_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15));
v___x_2561_ = l_Lean_stringToMessageData(v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2562_, lean_object* v_val_2563_, lean_object* v_upperBound_2564_, lean_object* v_args_2565_, lean_object* v_e_2566_, lean_object* v_next_2567_, lean_object* v_params_2568_, lean_object* v___x_2569_, uint8_t v___x_2570_, lean_object* v_a_2571_, lean_object* v_b_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_a_2579_; lean_object* v___y_2584_; uint8_t v___x_2603_; 
v___x_2603_ = lean_nat_dec_lt(v_a_2571_, v_upperBound_2564_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; 
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v___x_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2604_, 0, v_b_2572_);
return v___x_2604_;
}
else
{
lean_object* v___x_2605_; 
v___x_2605_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2562_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref(v___x_2605_);
v___x_2607_ = lean_box(0);
v___x_2608_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2563_, v_a_2571_, v_a_2606_);
lean_dec(v_a_2606_);
if (v___x_2608_ == 0)
{
v_a_2579_ = v___x_2607_;
goto v___jp_2578_;
}
else
{
lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2609_ = lean_array_get_size(v_args_2565_);
v___x_2610_ = lean_nat_dec_lt(v_a_2571_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2612_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg(v___x_2611_, v___y_2575_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; uint8_t v___x_2614_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref(v___x_2612_);
v___x_2614_ = lean_unbox(v_a_2613_);
lean_dec(v_a_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; 
lean_inc(v_a_2571_);
v___x_2615_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2562_, v_val_2563_, v_a_2571_, v___x_2607_, v___x_2607_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
v___y_2584_ = v___x_2615_;
goto v___jp_2583_;
}
else
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2616_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5);
lean_inc(v_val_2563_);
v___x_2617_ = l_Nat_reprFast(v_val_2563_);
v___x_2618_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
v___x_2619_ = l_Lean_MessageData_ofFormat(v___x_2618_);
v___x_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2616_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2620_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
lean_inc(v_a_2571_);
v___x_2623_ = l_Nat_reprFast(v_a_2571_);
v___x_2624_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
v___x_2625_ = l_Lean_MessageData_ofFormat(v___x_2624_);
lean_inc_ref(v___x_2625_);
v___x_2626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2622_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
v___x_2628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2626_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
lean_inc_ref(v_e_2566_);
v___x_2629_ = l_Lean_MessageData_ofExpr(v_e_2566_);
v___x_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10);
v___x_2632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2630_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v___x_2625_);
v___x_2634_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2611_, v___x_2633_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2636_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref(v___x_2634_);
lean_inc(v_a_2571_);
v___x_2636_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2562_, v_val_2563_, v_a_2571_, v___x_2607_, v_a_2635_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
v___y_2584_ = v___x_2636_;
goto v___jp_2583_;
}
else
{
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
return v___x_2634_;
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2637_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2612_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2612_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v___x_2645_; 
v___x_2645_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2562_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2645_);
v___x_2647_ = lean_array_fget_borrowed(v_args_2565_, v_a_2571_);
v___x_2648_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2563_, v_a_2571_, v_next_2567_, v_a_2646_);
lean_dec(v_a_2646_);
if (lean_obj_tag(v___x_2648_) == 1)
{
lean_object* v_val_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2782_; 
v_val_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2782_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_val_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2782_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; uint8_t v_foApprox_2654_; uint8_t v_ctxApprox_2655_; uint8_t v_quasiPatternApprox_2656_; uint8_t v_constApprox_2657_; uint8_t v_isDefEqStuckEx_2658_; uint8_t v_unificationHints_2659_; uint8_t v_assignSyntheticOpaque_2660_; uint8_t v_offsetCnstrs_2661_; uint8_t v_transparency_2662_; uint8_t v_etaStruct_2663_; uint8_t v_univApprox_2664_; uint8_t v_iota_2665_; uint8_t v_beta_2666_; uint8_t v_proj_2667_; uint8_t v_zeta_2668_; uint8_t v_zetaDelta_2669_; uint8_t v_zetaUnused_2670_; uint8_t v_zetaHave_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2781_; 
v___x_2653_ = l_Lean_Meta_Context_config(v___y_2573_);
v_foApprox_2654_ = lean_ctor_get_uint8(v___x_2653_, 0);
v_ctxApprox_2655_ = lean_ctor_get_uint8(v___x_2653_, 1);
v_quasiPatternApprox_2656_ = lean_ctor_get_uint8(v___x_2653_, 2);
v_constApprox_2657_ = lean_ctor_get_uint8(v___x_2653_, 3);
v_isDefEqStuckEx_2658_ = lean_ctor_get_uint8(v___x_2653_, 4);
v_unificationHints_2659_ = lean_ctor_get_uint8(v___x_2653_, 5);
v_assignSyntheticOpaque_2660_ = lean_ctor_get_uint8(v___x_2653_, 7);
v_offsetCnstrs_2661_ = lean_ctor_get_uint8(v___x_2653_, 8);
v_transparency_2662_ = lean_ctor_get_uint8(v___x_2653_, 9);
v_etaStruct_2663_ = lean_ctor_get_uint8(v___x_2653_, 10);
v_univApprox_2664_ = lean_ctor_get_uint8(v___x_2653_, 11);
v_iota_2665_ = lean_ctor_get_uint8(v___x_2653_, 12);
v_beta_2666_ = lean_ctor_get_uint8(v___x_2653_, 13);
v_proj_2667_ = lean_ctor_get_uint8(v___x_2653_, 14);
v_zeta_2668_ = lean_ctor_get_uint8(v___x_2653_, 15);
v_zetaDelta_2669_ = lean_ctor_get_uint8(v___x_2653_, 16);
v_zetaUnused_2670_ = lean_ctor_get_uint8(v___x_2653_, 17);
v_zetaHave_2671_ = lean_ctor_get_uint8(v___x_2653_, 18);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2673_ = v___x_2653_;
v_isShared_2674_ = v_isSharedCheck_2781_;
goto v_resetjp_2672_;
}
else
{
lean_dec(v___x_2653_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2781_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
uint8_t v_trackZetaDelta_2675_; lean_object* v_zetaDeltaSet_2676_; lean_object* v_lctx_2677_; lean_object* v_localInstances_2678_; lean_object* v_defEqCtx_x3f_2679_; lean_object* v_synthPendingDepth_2680_; lean_object* v_canUnfold_x3f_2681_; uint8_t v_univApprox_2682_; uint8_t v_inTypeClassResolution_2683_; uint8_t v_cacheInferType_2684_; uint8_t v___x_2685_; lean_object* v___x_2687_; 
v_trackZetaDelta_2675_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*7);
v_zetaDeltaSet_2676_ = lean_ctor_get(v___y_2573_, 1);
v_lctx_2677_ = lean_ctor_get(v___y_2573_, 2);
v_localInstances_2678_ = lean_ctor_get(v___y_2573_, 3);
v_defEqCtx_x3f_2679_ = lean_ctor_get(v___y_2573_, 4);
v_synthPendingDepth_2680_ = lean_ctor_get(v___y_2573_, 5);
v_canUnfold_x3f_2681_ = lean_ctor_get(v___y_2573_, 6);
v_univApprox_2682_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2683_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*7 + 2);
v_cacheInferType_2684_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*7 + 3);
v___x_2685_ = 0;
if (v_isShared_2674_ == 0)
{
v___x_2687_ = v___x_2673_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 0, v_foApprox_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 1, v_ctxApprox_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 2, v_quasiPatternApprox_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 3, v_constApprox_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 4, v_isDefEqStuckEx_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 5, v_unificationHints_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 7, v_assignSyntheticOpaque_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 8, v_offsetCnstrs_2661_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 9, v_transparency_2662_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 10, v_etaStruct_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 11, v_univApprox_2664_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 12, v_iota_2665_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 13, v_beta_2666_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 14, v_proj_2667_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 15, v_zeta_2668_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 16, v_zetaDelta_2669_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 17, v_zetaUnused_2670_);
lean_ctor_set_uint8(v_reuseFailAlloc_2780_, 18, v_zetaHave_2671_);
v___x_2687_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
uint64_t v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v_foApprox_2692_; uint8_t v_ctxApprox_2693_; uint8_t v_quasiPatternApprox_2694_; uint8_t v_constApprox_2695_; uint8_t v_isDefEqStuckEx_2696_; uint8_t v_unificationHints_2697_; uint8_t v_proofIrrelevance_2698_; uint8_t v_assignSyntheticOpaque_2699_; uint8_t v_offsetCnstrs_2700_; uint8_t v_etaStruct_2701_; uint8_t v_univApprox_2702_; uint8_t v_iota_2703_; uint8_t v_beta_2704_; uint8_t v_proj_2705_; uint8_t v_zeta_2706_; uint8_t v_zetaDelta_2707_; uint8_t v_zetaUnused_2708_; uint8_t v_zetaHave_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2779_; 
lean_ctor_set_uint8(v___x_2687_, 6, v___x_2685_);
v___x_2688_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2687_);
v___x_2689_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set_uint64(v___x_2689_, sizeof(void*)*1, v___x_2688_);
lean_inc(v_canUnfold_x3f_2681_);
lean_inc(v_synthPendingDepth_2680_);
lean_inc(v_defEqCtx_x3f_2679_);
lean_inc_ref(v_localInstances_2678_);
lean_inc_ref(v_lctx_2677_);
lean_inc(v_zetaDeltaSet_2676_);
v___x_2690_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v_zetaDeltaSet_2676_);
lean_ctor_set(v___x_2690_, 2, v_lctx_2677_);
lean_ctor_set(v___x_2690_, 3, v_localInstances_2678_);
lean_ctor_set(v___x_2690_, 4, v_defEqCtx_x3f_2679_);
lean_ctor_set(v___x_2690_, 5, v_synthPendingDepth_2680_);
lean_ctor_set(v___x_2690_, 6, v_canUnfold_x3f_2681_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*7, v_trackZetaDelta_2675_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*7 + 1, v_univApprox_2682_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2683_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*7 + 3, v_cacheInferType_2684_);
v___x_2691_ = l_Lean_Meta_Context_config(v___x_2690_);
v_foApprox_2692_ = lean_ctor_get_uint8(v___x_2691_, 0);
v_ctxApprox_2693_ = lean_ctor_get_uint8(v___x_2691_, 1);
v_quasiPatternApprox_2694_ = lean_ctor_get_uint8(v___x_2691_, 2);
v_constApprox_2695_ = lean_ctor_get_uint8(v___x_2691_, 3);
v_isDefEqStuckEx_2696_ = lean_ctor_get_uint8(v___x_2691_, 4);
v_unificationHints_2697_ = lean_ctor_get_uint8(v___x_2691_, 5);
v_proofIrrelevance_2698_ = lean_ctor_get_uint8(v___x_2691_, 6);
v_assignSyntheticOpaque_2699_ = lean_ctor_get_uint8(v___x_2691_, 7);
v_offsetCnstrs_2700_ = lean_ctor_get_uint8(v___x_2691_, 8);
v_etaStruct_2701_ = lean_ctor_get_uint8(v___x_2691_, 10);
v_univApprox_2702_ = lean_ctor_get_uint8(v___x_2691_, 11);
v_iota_2703_ = lean_ctor_get_uint8(v___x_2691_, 12);
v_beta_2704_ = lean_ctor_get_uint8(v___x_2691_, 13);
v_proj_2705_ = lean_ctor_get_uint8(v___x_2691_, 14);
v_zeta_2706_ = lean_ctor_get_uint8(v___x_2691_, 15);
v_zetaDelta_2707_ = lean_ctor_get_uint8(v___x_2691_, 16);
v_zetaUnused_2708_ = lean_ctor_get_uint8(v___x_2691_, 17);
v_zetaHave_2709_ = lean_ctor_get_uint8(v___x_2691_, 18);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2711_ = v___x_2691_;
v_isShared_2712_ = v_isSharedCheck_2779_;
goto v_resetjp_2710_;
}
else
{
lean_dec(v___x_2691_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2779_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; lean_object* v_config_2717_; 
v___x_2713_ = l_Lean_instInhabitedExpr;
v___x_2714_ = lean_array_get_borrowed(v___x_2713_, v_params_2568_, v_val_2649_);
lean_dec(v_val_2649_);
v___x_2715_ = 2;
if (v_isShared_2712_ == 0)
{
v_config_2717_ = v___x_2711_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 0, v_foApprox_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 1, v_ctxApprox_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 2, v_quasiPatternApprox_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 3, v_constApprox_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 4, v_isDefEqStuckEx_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 5, v_unificationHints_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 6, v_proofIrrelevance_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 7, v_assignSyntheticOpaque_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 8, v_offsetCnstrs_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 10, v_etaStruct_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 11, v_univApprox_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 12, v_iota_2703_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 13, v_beta_2704_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 14, v_proj_2705_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 15, v_zeta_2706_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 16, v_zetaDelta_2707_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 17, v_zetaUnused_2708_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, 18, v_zetaHave_2709_);
v_config_2717_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
uint64_t v___x_2718_; uint64_t v___x_2719_; uint64_t v___x_2720_; uint64_t v___x_2721_; uint64_t v___x_2722_; uint64_t v_key_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_ctor_set_uint8(v_config_2717_, 9, v___x_2715_);
v___x_2718_ = l_Lean_Meta_Context_configKey(v___x_2690_);
lean_dec_ref(v___x_2690_);
v___x_2719_ = 2ULL;
v___x_2720_ = lean_uint64_shift_right(v___x_2718_, v___x_2719_);
v___x_2721_ = lean_uint64_shift_left(v___x_2720_, v___x_2719_);
v___x_2722_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0);
v_key_2723_ = lean_uint64_lor(v___x_2721_, v___x_2722_);
v___x_2724_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2724_, 0, v_config_2717_);
lean_ctor_set_uint64(v___x_2724_, sizeof(void*)*1, v_key_2723_);
lean_inc(v_canUnfold_x3f_2681_);
lean_inc(v_synthPendingDepth_2680_);
lean_inc(v_defEqCtx_x3f_2679_);
lean_inc_ref(v_localInstances_2678_);
lean_inc_ref(v_lctx_2677_);
lean_inc(v_zetaDeltaSet_2676_);
v___x_2725_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v_zetaDeltaSet_2676_);
lean_ctor_set(v___x_2725_, 2, v_lctx_2677_);
lean_ctor_set(v___x_2725_, 3, v_localInstances_2678_);
lean_ctor_set(v___x_2725_, 4, v_defEqCtx_x3f_2679_);
lean_ctor_set(v___x_2725_, 5, v_synthPendingDepth_2680_);
lean_ctor_set(v___x_2725_, 6, v_canUnfold_x3f_2681_);
lean_ctor_set_uint8(v___x_2725_, sizeof(void*)*7, v_trackZetaDelta_2675_);
lean_ctor_set_uint8(v___x_2725_, sizeof(void*)*7 + 1, v_univApprox_2682_);
lean_ctor_set_uint8(v___x_2725_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2683_);
lean_ctor_set_uint8(v___x_2725_, sizeof(void*)*7 + 3, v_cacheInferType_2684_);
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
lean_inc(v___y_2574_);
lean_inc(v___x_2647_);
lean_inc(v___x_2714_);
v___x_2726_ = l_Lean_Meta_isExprDefEq(v___x_2714_, v___x_2647_, v___x_2725_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; uint8_t v___x_2728_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref(v___x_2726_);
v___x_2728_ = lean_unbox(v_a_2727_);
lean_dec(v_a_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2730_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg(v___x_2729_, v___y_2575_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; uint8_t v___x_2732_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref(v___x_2730_);
v___x_2732_ = lean_unbox(v_a_2731_);
lean_dec(v_a_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; 
lean_del_object(v___x_2651_);
lean_inc(v_a_2571_);
v___x_2733_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2562_, v_val_2563_, v_a_2571_, v___x_2607_, v___x_2607_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
v___y_2584_ = v___x_2733_;
goto v___jp_2583_;
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5);
lean_inc(v_val_2563_);
v___x_2735_ = l_Nat_reprFast(v_val_2563_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set_tag(v___x_2651_, 3);
lean_ctor_set(v___x_2651_, 0, v___x_2735_);
v___x_2737_ = v___x_2651_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2738_ = l_Lean_MessageData_ofFormat(v___x_2737_);
v___x_2739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2734_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
lean_inc(v_a_2571_);
v___x_2742_ = l_Nat_reprFast(v_a_2571_);
v___x_2743_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
v___x_2744_ = l_Lean_MessageData_ofFormat(v___x_2743_);
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2741_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
v___x_2747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
lean_inc_ref(v_e_2566_);
v___x_2748_ = l_Lean_MessageData_ofExpr(v_e_2566_);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
lean_inc(v___x_2714_);
v___x_2752_ = l_Lean_MessageData_ofExpr(v___x_2714_);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
lean_inc(v___x_2647_);
v___x_2756_ = l_Lean_MessageData_ofExpr(v___x_2647_);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2729_, v___x_2757_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2760_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref(v___x_2758_);
lean_inc(v_a_2571_);
v___x_2760_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2562_, v_val_2563_, v_a_2571_, v___x_2607_, v_a_2759_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
v___y_2584_ = v___x_2760_;
goto v___jp_2583_;
}
else
{
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
return v___x_2758_;
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_del_object(v___x_2651_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2762_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2730_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2730_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_del_object(v___x_2651_);
v_a_2579_ = v___x_2607_;
goto v___jp_2578_;
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_del_object(v___x_2651_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2770_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2726_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2726_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
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
lean_object* v___x_2783_; uint8_t v___x_2784_; lean_object* v___x_2785_; 
lean_dec(v___x_2648_);
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = 0;
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
lean_inc(v___y_2574_);
lean_inc(v_a_2571_);
lean_inc(v___x_2647_);
v___x_2785_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v___x_2569_, v_val_2562_, v_next_2567_, v_params_2568_, v___x_2647_, v_val_2563_, v_a_2571_, v___x_2570_, v___x_2783_, v___x_2784_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; uint8_t v___x_2787_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref(v___x_2785_);
v___x_2787_ = lean_unbox(v_a_2786_);
lean_dec(v_a_2786_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2789_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg(v___x_2788_, v___y_2575_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; uint8_t v___x_2791_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref(v___x_2789_);
v___x_2791_ = lean_unbox(v_a_2790_);
lean_dec(v_a_2790_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; 
lean_inc(v_a_2571_);
v___x_2792_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2562_, v_val_2563_, v_a_2571_, v___x_2607_, v___x_2607_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
v___y_2584_ = v___x_2792_;
goto v___jp_2583_;
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2793_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5);
lean_inc(v_val_2563_);
v___x_2794_ = l_Nat_reprFast(v_val_2563_);
v___x_2795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2794_);
v___x_2796_ = l_Lean_MessageData_ofFormat(v___x_2795_);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2793_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
lean_inc(v_a_2571_);
v___x_2800_ = l_Nat_reprFast(v_a_2571_);
v___x_2801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
v___x_2802_ = l_Lean_MessageData_ofFormat(v___x_2801_);
v___x_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2799_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
lean_inc_ref(v_e_2566_);
v___x_2806_ = l_Lean_MessageData_ofExpr(v_e_2566_);
v___x_2807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2805_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12);
v___x_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2807_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
lean_inc(v___x_2647_);
v___x_2810_ = l_Lean_MessageData_ofExpr(v___x_2647_);
v___x_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2788_, v___x_2813_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___x_2814_);
lean_inc(v_a_2571_);
v___x_2816_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2562_, v_val_2563_, v_a_2571_, v___x_2607_, v_a_2815_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
v___y_2584_ = v___x_2816_;
goto v___jp_2583_;
}
else
{
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
return v___x_2814_;
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2817_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2789_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2789_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
else
{
v_a_2579_ = v___x_2607_;
goto v___jp_2578_;
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2825_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2785_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2785_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2833_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2645_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2645_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2841_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2605_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2605_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
v___jp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_unsigned_to_nat(1u);
v___x_2581_ = lean_nat_add(v_a_2571_, v___x_2580_);
lean_dec(v_a_2571_);
v_a_2571_ = v___x_2581_;
v_b_2572_ = v_a_2579_;
goto _start;
}
v___jp_2583_:
{
if (lean_obj_tag(v___y_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2594_; 
v_a_2585_ = lean_ctor_get(v___y_2584_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___y_2584_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2587_ = v___y_2584_;
v_isShared_2588_ = v_isSharedCheck_2594_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___y_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2594_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
if (lean_obj_tag(v_a_2585_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; 
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2589_ = lean_ctor_get(v_a_2585_, 0);
lean_inc(v_a_2589_);
lean_dec_ref(v_a_2585_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 0, v_a_2589_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
else
{
lean_object* v_a_2593_; 
lean_del_object(v___x_2587_);
v_a_2593_ = lean_ctor_get(v_a_2585_, 0);
lean_inc(v_a_2593_);
lean_dec_ref(v_a_2585_);
v_a_2579_ = v_a_2593_;
goto v___jp_2578_;
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2595_ = lean_ctor_get(v___y_2584_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___y_2584_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___y_2584_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___y_2584_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2849_, lean_object* v_val_2850_, lean_object* v_upperBound_2851_, lean_object* v_args_2852_, lean_object* v_e_2853_, lean_object* v_next_2854_, lean_object* v_params_2855_, lean_object* v___x_2856_, lean_object* v___x_2857_, lean_object* v_a_2858_, lean_object* v_b_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
uint8_t v___x_42810__boxed_2865_; lean_object* v_res_2866_; 
v___x_42810__boxed_2865_ = lean_unbox(v___x_2857_);
v_res_2866_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2849_, v_val_2850_, v_upperBound_2851_, v_args_2852_, v_e_2853_, v_next_2854_, v_params_2855_, v___x_2856_, v___x_42810__boxed_2865_, v_a_2858_, v_b_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
lean_dec_ref(v___y_2860_);
lean_dec(v___x_2856_);
lean_dec_ref(v_params_2855_);
lean_dec(v_next_2854_);
lean_dec_ref(v_args_2852_);
lean_dec(v_upperBound_2851_);
lean_dec(v_val_2849_);
return v_res_2866_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___lam__0(lean_object* v___x_2867_, lean_object* v_x_2868_){
_start:
{
lean_object* v_declName_2869_; uint8_t v___x_2870_; 
v_declName_2869_ = lean_ctor_get(v_x_2868_, 3);
v___x_2870_ = lean_name_eq(v_declName_2869_, v___x_2867_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___lam__0___boxed(lean_object* v___x_2871_, lean_object* v_x_2872_){
_start:
{
uint8_t v_res_2873_; lean_object* v_r_2874_; 
v_res_2873_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___lam__0(v___x_2871_, v_x_2872_);
lean_dec_ref(v_x_2872_);
lean_dec(v___x_2871_);
v_r_2874_ = lean_box(v_res_2873_);
return v_r_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2877_, lean_object* v___x_2878_, lean_object* v_val_2879_, lean_object* v_e_2880_, lean_object* v_next_2881_, lean_object* v_params_2882_, lean_object* v___x_2883_, lean_object* v_x_2884_, lean_object* v_x_2885_, lean_object* v_x_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
if (lean_obj_tag(v_x_2884_) == 5)
{
lean_object* v_fn_2892_; lean_object* v_arg_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_fn_2892_ = lean_ctor_get(v_x_2884_, 0);
lean_inc_ref(v_fn_2892_);
v_arg_2893_ = lean_ctor_get(v_x_2884_, 1);
lean_inc_ref(v_arg_2893_);
lean_dec_ref(v_x_2884_);
v___x_2894_ = lean_array_set(v_x_2885_, v_x_2886_, v_arg_2893_);
v___x_2895_ = lean_unsigned_to_nat(1u);
v___x_2896_ = lean_nat_sub(v_x_2886_, v___x_2895_);
lean_dec(v_x_2886_);
v_x_2884_ = v_fn_2892_;
v_x_2885_ = v___x_2894_;
v_x_2886_ = v___x_2896_;
goto _start;
}
else
{
uint8_t v___x_2898_; 
lean_dec(v_x_2886_);
v___x_2898_ = l_Lean_Expr_isConst(v_x_2884_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v_x_2885_);
lean_dec_ref(v_x_2884_);
lean_dec_ref(v_e_2880_);
v___x_2899_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
return v___x_2900_;
}
else
{
lean_object* v___x_2901_; lean_object* v___f_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2901_ = l_Lean_Expr_constName_x21(v_x_2884_);
lean_dec_ref(v_x_2884_);
v___f_2902_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2902_, 0, v___x_2901_);
v___x_2903_ = lean_unsigned_to_nat(0u);
v___x_2904_ = l_Array_findIdx_x3f_loop___redArg(v___f_2902_, v_preDefs_2877_, v___x_2903_);
if (lean_obj_tag(v___x_2904_) == 1)
{
lean_object* v_val_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_val_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_val_2905_);
lean_dec_ref(v___x_2904_);
v___x_2906_ = lean_box(0);
v___x_2907_ = lean_array_get_borrowed(v___x_2903_, v___x_2878_, v_val_2905_);
v___x_2908_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2879_, v_val_2905_, v___x_2907_, v_x_2885_, v_e_2880_, v_next_2881_, v_params_2882_, v___x_2883_, v___x_2898_, v___x_2903_, v___x_2906_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec_ref(v_x_2885_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2916_; 
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; 
v_unused_2917_ = lean_ctor_get(v___x_2908_, 0);
lean_dec(v_unused_2917_);
v___x_2910_ = v___x_2908_;
v_isShared_2911_ = v_isSharedCheck_2916_;
goto v_resetjp_2909_;
}
else
{
lean_dec(v___x_2908_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2916_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2912_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 0, v___x_2912_);
v___x_2914_ = v___x_2910_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
v_a_2918_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2908_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2908_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_dec(v___x_2904_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v_x_2885_);
lean_dec_ref(v_e_2880_);
v___x_2926_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
return v___x_2927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2928_, lean_object* v___x_2929_, lean_object* v_val_2930_, lean_object* v_e_2931_, lean_object* v_next_2932_, lean_object* v_params_2933_, lean_object* v___x_2934_, lean_object* v_x_2935_, lean_object* v_x_2936_, lean_object* v_x_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2928_, v___x_2929_, v_val_2930_, v_e_2931_, v_next_2932_, v_params_2933_, v___x_2934_, v_x_2935_, v_x_2936_, v_x_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec_ref(v___y_2938_);
lean_dec(v___x_2934_);
lean_dec_ref(v_params_2933_);
lean_dec(v_next_2932_);
lean_dec(v_val_2930_);
lean_dec_ref(v___x_2929_);
lean_dec_ref(v_preDefs_2928_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2944_, lean_object* v___x_2945_, lean_object* v_val_2946_, lean_object* v_a_2947_, lean_object* v_params_2948_, lean_object* v___x_2949_, lean_object* v_e_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_dummy_2956_; lean_object* v_nargs_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_dummy_2956_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2957_ = l_Lean_Expr_getAppNumArgs(v_e_2950_);
lean_inc(v_nargs_2957_);
v___x_2958_ = lean_mk_array(v_nargs_2957_, v_dummy_2956_);
v___x_2959_ = lean_unsigned_to_nat(1u);
v___x_2960_ = lean_nat_sub(v_nargs_2957_, v___x_2959_);
lean_dec(v_nargs_2957_);
lean_inc_ref(v_e_2950_);
v___x_2961_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2944_, v___x_2945_, v_val_2946_, v_e_2950_, v_a_2947_, v_params_2948_, v___x_2949_, v_e_2950_, v___x_2958_, v___x_2960_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2962_, lean_object* v___x_2963_, lean_object* v_val_2964_, lean_object* v_a_2965_, lean_object* v_params_2966_, lean_object* v___x_2967_, lean_object* v_e_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2962_, v___x_2963_, v_val_2964_, v_a_2965_, v_params_2966_, v___x_2967_, v_e_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec_ref(v___y_2969_);
lean_dec(v___x_2967_);
lean_dec_ref(v_params_2966_);
lean_dec(v_a_2965_);
lean_dec(v_val_2964_);
lean_dec_ref(v___x_2963_);
lean_dec_ref(v_preDefs_2962_);
return v_res_2974_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2978_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2979_ = lean_unsigned_to_nat(6u);
v___x_2980_ = lean_unsigned_to_nat(201u);
v___x_2981_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2982_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2983_ = l_mkPanicMessageWithDecl(v___x_2982_, v___x_2981_, v___x_2980_, v___x_2979_, v___x_2978_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2984_, lean_object* v___x_2985_, lean_object* v_a_2986_, lean_object* v_preDefs_2987_, lean_object* v_val_2988_, lean_object* v___f_2989_, lean_object* v___x_2990_, lean_object* v_params_2991_, lean_object* v_body_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2998_ = lean_array_get_size(v_params_2991_);
v___x_2999_ = lean_array_get_borrowed(v___x_2984_, v___x_2985_, v_a_2986_);
v___x_3000_ = lean_nat_dec_eq(v___x_2998_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
lean_dec_ref(v_body_2992_);
lean_dec_ref(v_params_2991_);
lean_dec_ref(v___f_2989_);
lean_dec(v_val_2988_);
lean_dec_ref(v_preDefs_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v___x_2985_);
v___x_3001_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_3002_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3001_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
return v___x_3002_;
}
else
{
lean_object* v___f_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; 
v___f_3003_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_3003_, 0, v_preDefs_2987_);
lean_closure_set(v___f_3003_, 1, v___x_2985_);
lean_closure_set(v___f_3003_, 2, v_val_2988_);
lean_closure_set(v___f_3003_, 3, v_a_2986_);
lean_closure_set(v___f_3003_, 4, v_params_2991_);
lean_closure_set(v___f_3003_, 5, v___x_2998_);
v___x_3004_ = 0;
v___x_3005_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2992_, v___f_3003_, v___f_2989_, v___x_3004_, v___x_3000_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3012_ == 0)
{
lean_object* v_unused_3013_; 
v_unused_3013_ = lean_ctor_get(v___x_3005_, 0);
lean_dec(v_unused_3013_);
v___x_3007_ = v___x_3005_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_dec(v___x_3005_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_2990_);
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_2990_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
v_a_3014_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_3005_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3005_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_3022_, lean_object* v___x_3023_, lean_object* v_a_3024_, lean_object* v_preDefs_3025_, lean_object* v_val_3026_, lean_object* v___f_3027_, lean_object* v___x_3028_, lean_object* v_params_3029_, lean_object* v_body_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_3022_, v___x_3023_, v_a_3024_, v_preDefs_3025_, v_val_3026_, v___f_3027_, v___x_3028_, v_params_3029_, v_body_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3043_, 0, v_e_3037_);
v___x_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v_preDefs_3053_, lean_object* v___x_3054_, lean_object* v_val_3055_, lean_object* v_upperBound_3056_, lean_object* v_a_3057_, lean_object* v_b_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
uint8_t v___x_3064_; 
v___x_3064_ = lean_nat_dec_lt(v_a_3057_, v_upperBound_3056_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; 
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v_a_3057_);
lean_dec(v_val_3055_);
lean_dec_ref(v___x_3054_);
lean_dec_ref(v_preDefs_3053_);
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v_b_3058_);
return v___x_3065_;
}
else
{
lean_object* v___x_3066_; lean_object* v_value_3067_; lean_object* v___f_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___f_3071_; uint8_t v___x_3072_; lean_object* v___x_3073_; 
v___x_3066_ = lean_array_fget_borrowed(v_preDefs_3053_, v_a_3057_);
v_value_3067_ = lean_ctor_get(v___x_3066_, 7);
v___f_3068_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3069_ = lean_unsigned_to_nat(0u);
v___x_3070_ = lean_box(0);
lean_inc(v_val_3055_);
lean_inc_ref(v_preDefs_3053_);
lean_inc(v_a_3057_);
lean_inc_ref(v___x_3054_);
v___f_3071_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3071_, 0, v___x_3069_);
lean_closure_set(v___f_3071_, 1, v___x_3054_);
lean_closure_set(v___f_3071_, 2, v_a_3057_);
lean_closure_set(v___f_3071_, 3, v_preDefs_3053_);
lean_closure_set(v___f_3071_, 4, v_val_3055_);
lean_closure_set(v___f_3071_, 5, v___f_3068_);
lean_closure_set(v___f_3071_, 6, v___x_3070_);
v___x_3072_ = 0;
lean_inc(v___y_3062_);
lean_inc_ref(v___y_3061_);
lean_inc(v___y_3060_);
lean_inc_ref(v___y_3059_);
lean_inc_ref(v_value_3067_);
v___x_3073_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_3067_, v___f_3071_, v___x_3072_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_dec_ref(v___x_3073_);
v___x_3074_ = lean_unsigned_to_nat(1u);
v___x_3075_ = lean_nat_add(v_a_3057_, v___x_3074_);
lean_dec(v_a_3057_);
v_a_3057_ = v___x_3075_;
v_b_3058_ = v___x_3070_;
goto _start;
}
else
{
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v_a_3057_);
lean_dec(v_val_3055_);
lean_dec_ref(v___x_3054_);
lean_dec_ref(v_preDefs_3053_);
return v___x_3073_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v_preDefs_3077_, lean_object* v___x_3078_, lean_object* v_val_3079_, lean_object* v_upperBound_3080_, lean_object* v_a_3081_, lean_object* v_b_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3077_, v___x_3078_, v_val_3079_, v_upperBound_3080_, v_a_3081_, v_b_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v_upperBound_3080_);
return v_res_3088_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3091_ = l_Lean_stringToMessageData(v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_){
_start:
{
size_t v_sz_3098_; size_t v___x_3099_; lean_object* v___x_3100_; 
v_sz_3098_ = lean_array_size(v_preDefs_3092_);
v___x_3099_ = ((size_t)0ULL);
lean_inc(v_a_3096_);
lean_inc_ref(v_a_3095_);
lean_inc(v_a_3094_);
lean_inc_ref(v_a_3093_);
lean_inc_ref(v_preDefs_3092_);
v___x_3100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3098_, v___x_3099_, v_preDefs_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; size_t v_sz_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref(v___x_3100_);
v_sz_3102_ = lean_array_size(v_a_3101_);
lean_inc(v_a_3101_);
v___x_3103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3102_, v___x_3099_, v_a_3101_);
v___x_3104_ = l_Lean_Elab_FixedParams_Info_init(v_a_3101_);
v___x_3105_ = lean_st_mk_ref(v___x_3104_);
v___x_3106_ = lean_st_ref_take(v___x_3105_);
v___x_3107_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3106_);
v___x_3108_ = lean_st_ref_set(v___x_3105_, v___x_3107_);
v___x_3109_ = lean_array_get_size(v_preDefs_3092_);
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_box(0);
lean_inc(v_a_3096_);
lean_inc_ref(v_a_3095_);
lean_inc(v_a_3094_);
lean_inc_ref(v_a_3093_);
lean_inc(v___x_3105_);
v___x_3112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3092_, v___x_3103_, v___x_3105_, v___x_3109_, v___x_3110_, v___x_3111_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3146_; 
lean_dec_ref(v___x_3112_);
v___x_3113_ = lean_st_ref_get(v___x_3105_);
lean_dec(v___x_3105_);
v___x_3114_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3115_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg(v___x_3114_, v_a_3095_);
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3146_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3146_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
uint8_t v___x_3120_; 
v___x_3120_ = lean_unbox(v_a_3116_);
lean_dec(v_a_3116_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3122_; 
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3113_);
v___x_3122_ = v___x_3118_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3113_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
else
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
lean_del_object(v___x_3118_);
v___x_3124_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3113_);
v___x_3125_ = l_Lean_Elab_FixedParams_Info_format(v___x_3113_);
v___x_3126_ = l_Std_Format_indentD(v___x_3125_);
v___x_3127_ = l_Lean_MessageData_ofFormat(v___x_3126_);
v___x_3128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3124_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
v___x_3129_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_3114_, v___x_3128_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v___x_3129_, 0);
lean_dec(v_unused_3137_);
v___x_3131_ = v___x_3129_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_dec(v___x_3129_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v___x_3113_);
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3113_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v___x_3113_);
v_a_3138_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3129_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3129_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v___x_3105_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
v_a_3147_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3112_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3112_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec_ref(v_preDefs_3092_);
v_a_3155_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3100_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3100_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_upperBound_3170_, lean_object* v_val_3171_, lean_object* v_next_3172_, lean_object* v_params_3173_, lean_object* v___x_3174_, lean_object* v_val_3175_, lean_object* v_next_3176_, uint8_t v___x_3177_, lean_object* v_inst_3178_, lean_object* v_R_3179_, lean_object* v_a_3180_, uint8_t v_b_3181_, lean_object* v_c_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_3170_, v_val_3171_, v_next_3172_, v_params_3173_, v___x_3174_, v_val_3175_, v_next_3176_, v___x_3177_, v_a_3180_, v_b_3181_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3189_ = _args[0];
lean_object* v_val_3190_ = _args[1];
lean_object* v_next_3191_ = _args[2];
lean_object* v_params_3192_ = _args[3];
lean_object* v___x_3193_ = _args[4];
lean_object* v_val_3194_ = _args[5];
lean_object* v_next_3195_ = _args[6];
lean_object* v___x_3196_ = _args[7];
lean_object* v_inst_3197_ = _args[8];
lean_object* v_R_3198_ = _args[9];
lean_object* v_a_3199_ = _args[10];
lean_object* v_b_3200_ = _args[11];
lean_object* v_c_3201_ = _args[12];
lean_object* v___y_3202_ = _args[13];
lean_object* v___y_3203_ = _args[14];
lean_object* v___y_3204_ = _args[15];
lean_object* v___y_3205_ = _args[16];
lean_object* v___y_3206_ = _args[17];
_start:
{
uint8_t v___x_43812__boxed_3207_; uint8_t v_b_boxed_3208_; lean_object* v_res_3209_; 
v___x_43812__boxed_3207_ = lean_unbox(v___x_3196_);
v_b_boxed_3208_ = lean_unbox(v_b_3200_);
v_res_3209_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_upperBound_3189_, v_val_3190_, v_next_3191_, v_params_3192_, v___x_3193_, v_val_3194_, v_next_3195_, v___x_43812__boxed_3207_, v_inst_3197_, v_R_3198_, v_a_3199_, v_b_boxed_3208_, v_c_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec_ref(v___y_3202_);
lean_dec(v_val_3194_);
lean_dec_ref(v_params_3192_);
lean_dec(v_next_3191_);
lean_dec(v_val_3190_);
lean_dec(v_upperBound_3189_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3210_, lean_object* v_val_3211_, lean_object* v_upperBound_3212_, lean_object* v_args_3213_, lean_object* v_e_3214_, lean_object* v_next_3215_, lean_object* v_params_3216_, lean_object* v___x_3217_, uint8_t v___x_3218_, lean_object* v_inst_3219_, lean_object* v_R_3220_, lean_object* v_a_3221_, lean_object* v_b_3222_, lean_object* v_c_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3210_, v_val_3211_, v_upperBound_3212_, v_args_3213_, v_e_3214_, v_next_3215_, v_params_3216_, v___x_3217_, v___x_3218_, v_a_3221_, v_b_3222_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3230_ = _args[0];
lean_object* v_val_3231_ = _args[1];
lean_object* v_upperBound_3232_ = _args[2];
lean_object* v_args_3233_ = _args[3];
lean_object* v_e_3234_ = _args[4];
lean_object* v_next_3235_ = _args[5];
lean_object* v_params_3236_ = _args[6];
lean_object* v___x_3237_ = _args[7];
lean_object* v___x_3238_ = _args[8];
lean_object* v_inst_3239_ = _args[9];
lean_object* v_R_3240_ = _args[10];
lean_object* v_a_3241_ = _args[11];
lean_object* v_b_3242_ = _args[12];
lean_object* v_c_3243_ = _args[13];
lean_object* v___y_3244_ = _args[14];
lean_object* v___y_3245_ = _args[15];
lean_object* v___y_3246_ = _args[16];
lean_object* v___y_3247_ = _args[17];
lean_object* v___y_3248_ = _args[18];
_start:
{
uint8_t v___x_43847__boxed_3249_; lean_object* v_res_3250_; 
v___x_43847__boxed_3249_ = lean_unbox(v___x_3238_);
v_res_3250_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3230_, v_val_3231_, v_upperBound_3232_, v_args_3233_, v_e_3234_, v_next_3235_, v_params_3236_, v___x_3237_, v___x_43847__boxed_3249_, v_inst_3239_, v_R_3240_, v_a_3241_, v_b_3242_, v_c_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec_ref(v___y_3244_);
lean_dec(v___x_3237_);
lean_dec_ref(v_params_3236_);
lean_dec(v_next_3235_);
lean_dec_ref(v_args_3233_);
lean_dec(v_upperBound_3232_);
lean_dec(v_val_3230_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v_preDefs_3251_, lean_object* v___x_3252_, lean_object* v_val_3253_, lean_object* v_upperBound_3254_, lean_object* v_inst_3255_, lean_object* v_R_3256_, lean_object* v_a_3257_, lean_object* v_b_3258_, lean_object* v_c_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3251_, v___x_3252_, v_val_3253_, v_upperBound_3254_, v_a_3257_, v_b_3258_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v_preDefs_3266_, lean_object* v___x_3267_, lean_object* v_val_3268_, lean_object* v_upperBound_3269_, lean_object* v_inst_3270_, lean_object* v_R_3271_, lean_object* v_a_3272_, lean_object* v_b_3273_, lean_object* v_c_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v_preDefs_3266_, v___x_3267_, v_val_3268_, v_upperBound_3269_, v_inst_3270_, v_R_3271_, v_a_3272_, v_b_3273_, v_c_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
lean_dec(v_upperBound_3269_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3281_, lean_object* v___x_3282_, lean_object* v_pre_3283_, lean_object* v_post_3284_, uint8_t v_usedLetOnly_3285_, uint8_t v_skipConstInApp_3286_, uint8_t v_skipInstances_3287_, lean_object* v___x_3288_, lean_object* v_inst_3289_, lean_object* v_R_3290_, lean_object* v_a_3291_, lean_object* v_b_3292_, lean_object* v_c_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3281_, v___x_3282_, v_pre_3283_, v_post_3284_, v_usedLetOnly_3285_, v_skipConstInApp_3286_, v_skipInstances_3287_, v_a_3291_, v_b_3292_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3301_ = _args[0];
lean_object* v___x_3302_ = _args[1];
lean_object* v_pre_3303_ = _args[2];
lean_object* v_post_3304_ = _args[3];
lean_object* v_usedLetOnly_3305_ = _args[4];
lean_object* v_skipConstInApp_3306_ = _args[5];
lean_object* v_skipInstances_3307_ = _args[6];
lean_object* v___x_3308_ = _args[7];
lean_object* v_inst_3309_ = _args[8];
lean_object* v_R_3310_ = _args[9];
lean_object* v_a_3311_ = _args[10];
lean_object* v_b_3312_ = _args[11];
lean_object* v_c_3313_ = _args[12];
lean_object* v___y_3314_ = _args[13];
lean_object* v___y_3315_ = _args[14];
lean_object* v___y_3316_ = _args[15];
lean_object* v___y_3317_ = _args[16];
lean_object* v___y_3318_ = _args[17];
lean_object* v___y_3319_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3320_; uint8_t v_skipConstInApp_boxed_3321_; uint8_t v_skipInstances_boxed_3322_; lean_object* v_res_3323_; 
v_usedLetOnly_boxed_3320_ = lean_unbox(v_usedLetOnly_3305_);
v_skipConstInApp_boxed_3321_ = lean_unbox(v_skipConstInApp_3306_);
v_skipInstances_boxed_3322_ = lean_unbox(v_skipInstances_3307_);
v_res_3323_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3301_, v___x_3302_, v_pre_3303_, v_post_3304_, v_usedLetOnly_boxed_3320_, v_skipConstInApp_boxed_3321_, v_skipInstances_boxed_3322_, v___x_3308_, v_inst_3309_, v_R_3310_, v_a_3311_, v_b_3312_, v_c_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___x_3308_);
lean_dec_ref(v___x_3302_);
lean_dec(v_upperBound_3301_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3324_, lean_object* v_m_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3325_, v_a_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3328_, lean_object* v_m_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3328_, v_m_3329_, v_a_3330_);
lean_dec_ref(v_a_3330_);
lean_dec_ref(v_m_3329_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3332_, lean_object* v_name_3333_, uint8_t v_bi_3334_, lean_object* v_type_3335_, lean_object* v_k_3336_, uint8_t v_kind_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3333_, v_bi_3334_, v_type_3335_, v_k_3336_, v_kind_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3345_, lean_object* v_name_3346_, lean_object* v_bi_3347_, lean_object* v_type_3348_, lean_object* v_k_3349_, lean_object* v_kind_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
uint8_t v_bi_boxed_3357_; uint8_t v_kind_boxed_3358_; lean_object* v_res_3359_; 
v_bi_boxed_3357_ = lean_unbox(v_bi_3347_);
v_kind_boxed_3358_ = lean_unbox(v_kind_3350_);
v_res_3359_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3345_, v_name_3346_, v_bi_boxed_3357_, v_type_3348_, v_k_3349_, v_kind_boxed_3358_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3360_, lean_object* v_name_3361_, lean_object* v_type_3362_, lean_object* v_val_3363_, lean_object* v_k_3364_, uint8_t v_nondep_3365_, uint8_t v_kind_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3361_, v_type_3362_, v_val_3363_, v_k_3364_, v_nondep_3365_, v_kind_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3374_, lean_object* v_name_3375_, lean_object* v_type_3376_, lean_object* v_val_3377_, lean_object* v_k_3378_, lean_object* v_nondep_3379_, lean_object* v_kind_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
uint8_t v_nondep_boxed_3387_; uint8_t v_kind_boxed_3388_; lean_object* v_res_3389_; 
v_nondep_boxed_3387_ = lean_unbox(v_nondep_3379_);
v_kind_boxed_3388_ = lean_unbox(v_kind_3380_);
v_res_3389_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3374_, v_name_3375_, v_type_3376_, v_val_3377_, v_k_3378_, v_nondep_boxed_3387_, v_kind_boxed_3388_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3390_, lean_object* v_ref_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v___x_3397_; 
v___x_3397_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3391_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3398_, lean_object* v_ref_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3398_, v_ref_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3406_, lean_object* v_x_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3415_, lean_object* v_x_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3415_, v_x_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3424_, lean_object* v_m_3425_, lean_object* v_a_3426_, lean_object* v_b_3427_){
_start:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3425_, v_a_3426_, v_b_3427_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3429_, lean_object* v_a_3430_, lean_object* v_x_3431_){
_start:
{
lean_object* v___x_3432_; 
v___x_3432_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3430_, v_x_3431_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3433_, lean_object* v_a_3434_, lean_object* v_x_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3433_, v_a_3434_, v_x_3435_);
lean_dec(v_x_3435_);
lean_dec_ref(v_a_3434_);
return v_res_3436_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3437_, lean_object* v_a_3438_, lean_object* v_x_3439_){
_start:
{
uint8_t v___x_3440_; 
v___x_3440_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3438_, v_x_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3441_, lean_object* v_a_3442_, lean_object* v_x_3443_){
_start:
{
uint8_t v_res_3444_; lean_object* v_r_3445_; 
v_res_3444_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3441_, v_a_3442_, v_x_3443_);
lean_dec(v_x_3443_);
lean_dec_ref(v_a_3442_);
v_r_3445_ = lean_box(v_res_3444_);
return v_r_3445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3446_, lean_object* v_data_3447_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3449_, lean_object* v_a_3450_, lean_object* v_b_3451_, lean_object* v_x_3452_){
_start:
{
lean_object* v___x_3453_; 
v___x_3453_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3450_, v_b_3451_, v_x_3452_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3454_, lean_object* v_i_3455_, lean_object* v_source_3456_, lean_object* v_target_3457_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3455_, v_source_3456_, v_target_3457_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3459_, lean_object* v_x_3460_, lean_object* v_x_3461_){
_start:
{
lean_object* v___x_3462_; 
v___x_3462_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3460_, v_x_3461_);
return v___x_3462_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3465_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__0));
v___x_3466_ = lean_unsigned_to_nat(0u);
v___x_3467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
lean_ctor_set(v___x_3467_, 1, v___x_3465_);
lean_ctor_set(v___x_3467_, 2, v___x_3465_);
return v___x_3467_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFixedParamPerms_default(void){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = lean_obj_once(&l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1, &l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1_once, _init_l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1);
return v___x_3468_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFixedParamPerms(void){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_Elab_instInhabitedFixedParamPerms_default;
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3476_, lean_object* v_x_3477_){
_start:
{
if (lean_obj_tag(v_x_3476_) == 0)
{
lean_object* v___x_3478_; 
v___x_3478_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3478_;
}
else
{
lean_object* v_val_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3490_; 
v_val_3479_ = lean_ctor_get(v_x_3476_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_x_3476_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3481_ = v_x_3476_;
v_isShared_3482_ = v_isSharedCheck_3490_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_val_3479_);
lean_dec(v_x_3476_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3490_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3483_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3484_ = l_Nat_reprFast(v_val_3479_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set_tag(v___x_3481_, 3);
lean_ctor_set(v___x_3481_, 0, v___x_3484_);
v___x_3486_ = v___x_3481_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3483_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = l_Repr_addAppParen(v___x_3487_, v_x_3477_);
return v___x_3488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3491_, lean_object* v_x_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3491_, v_x_3492_);
lean_dec(v_x_3492_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3494_, lean_object* v_x_3495_, lean_object* v_x_3496_){
_start:
{
if (lean_obj_tag(v_x_3496_) == 0)
{
lean_dec(v_x_3494_);
return v_x_3495_;
}
else
{
lean_object* v_head_3497_; lean_object* v_tail_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3509_; 
v_head_3497_ = lean_ctor_get(v_x_3496_, 0);
v_tail_3498_ = lean_ctor_get(v_x_3496_, 1);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_x_3496_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3500_ = v_x_3496_;
v_isShared_3501_ = v_isSharedCheck_3509_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_tail_3498_);
lean_inc(v_head_3497_);
lean_dec(v_x_3496_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3509_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
lean_inc(v_x_3494_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set_tag(v___x_3500_, 5);
lean_ctor_set(v___x_3500_, 1, v_x_3494_);
lean_ctor_set(v___x_3500_, 0, v_x_3495_);
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_x_3495_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_x_3494_);
v___x_3503_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = lean_unsigned_to_nat(0u);
v___x_3505_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3497_, v___x_3504_);
v___x_3506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3503_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v_x_3495_ = v___x_3506_;
v_x_3496_ = v_tail_3498_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3510_, lean_object* v_x_3511_, lean_object* v_x_3512_){
_start:
{
if (lean_obj_tag(v_x_3512_) == 0)
{
lean_dec(v_x_3510_);
return v_x_3511_;
}
else
{
lean_object* v_head_3513_; lean_object* v_tail_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3525_; 
v_head_3513_ = lean_ctor_get(v_x_3512_, 0);
v_tail_3514_ = lean_ctor_get(v_x_3512_, 1);
v_isSharedCheck_3525_ = !lean_is_exclusive(v_x_3512_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3516_ = v_x_3512_;
v_isShared_3517_ = v_isSharedCheck_3525_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_tail_3514_);
lean_inc(v_head_3513_);
lean_dec(v_x_3512_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3525_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
lean_inc(v_x_3510_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set_tag(v___x_3516_, 5);
lean_ctor_set(v___x_3516_, 1, v_x_3510_);
lean_ctor_set(v___x_3516_, 0, v_x_3511_);
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_x_3511_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_x_3510_);
v___x_3519_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3520_ = lean_unsigned_to_nat(0u);
v___x_3521_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3513_, v___x_3520_);
v___x_3522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3519_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3510_, v___x_3522_, v_tail_3514_);
return v___x_3523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = lean_unsigned_to_nat(0u);
v___x_3528_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3526_, v___x_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3529_, lean_object* v_x_3530_){
_start:
{
if (lean_obj_tag(v_x_3529_) == 0)
{
lean_object* v___x_3531_; 
lean_dec(v_x_3530_);
v___x_3531_ = lean_box(0);
return v___x_3531_;
}
else
{
lean_object* v_tail_3532_; 
v_tail_3532_ = lean_ctor_get(v_x_3529_, 1);
if (lean_obj_tag(v_tail_3532_) == 0)
{
lean_object* v_head_3533_; lean_object* v___x_3534_; 
lean_dec(v_x_3530_);
v_head_3533_ = lean_ctor_get(v_x_3529_, 0);
lean_inc(v_head_3533_);
lean_dec_ref(v_x_3529_);
v___x_3534_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3533_);
return v___x_3534_;
}
else
{
lean_object* v_head_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_inc(v_tail_3532_);
v_head_3535_ = lean_ctor_get(v_x_3529_, 0);
lean_inc(v_head_3535_);
lean_dec_ref(v_x_3529_);
v___x_3536_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3535_);
v___x_3537_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3530_, v___x_3536_, v_tail_3532_);
return v___x_3537_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3546_ = lean_string_length(v___x_3545_);
return v___x_3546_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3548_ = lean_nat_to_int(v___x_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3554_){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; uint8_t v___x_3557_; 
v___x_3555_ = lean_array_get_size(v_xs_3554_);
v___x_3556_ = lean_unsigned_to_nat(0u);
v___x_3557_ = lean_nat_dec_eq(v___x_3555_, v___x_3556_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3558_ = lean_array_to_list(v_xs_3554_);
v___x_3559_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3560_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3558_, v___x_3559_);
v___x_3561_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3562_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
lean_ctor_set(v___x_3563_, 1, v___x_3560_);
v___x_3564_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3563_);
lean_ctor_set(v___x_3565_, 1, v___x_3564_);
v___x_3566_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3561_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = l_Std_Format_fill(v___x_3566_);
return v___x_3567_;
}
else
{
lean_object* v___x_3568_; 
lean_dec_ref(v_xs_3554_);
v___x_3568_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3568_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3569_, lean_object* v_x_3570_, lean_object* v_x_3571_){
_start:
{
if (lean_obj_tag(v_x_3571_) == 0)
{
lean_dec(v_x_3569_);
return v_x_3570_;
}
else
{
lean_object* v_head_3572_; lean_object* v_tail_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3583_; 
v_head_3572_ = lean_ctor_get(v_x_3571_, 0);
v_tail_3573_ = lean_ctor_get(v_x_3571_, 1);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_x_3571_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3575_ = v_x_3571_;
v_isShared_3576_ = v_isSharedCheck_3583_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_tail_3573_);
lean_inc(v_head_3572_);
lean_dec(v_x_3571_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3583_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
lean_inc(v_x_3569_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set_tag(v___x_3575_, 5);
lean_ctor_set(v___x_3575_, 1, v_x_3569_);
lean_ctor_set(v___x_3575_, 0, v_x_3570_);
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_x_3570_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_x_3569_);
v___x_3578_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3572_);
v___x_3580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3578_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v_x_3570_ = v___x_3580_;
v_x_3571_ = v_tail_3573_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3584_, lean_object* v_x_3585_){
_start:
{
if (lean_obj_tag(v_x_3584_) == 0)
{
lean_object* v___x_3586_; 
lean_dec(v_x_3585_);
v___x_3586_ = lean_box(0);
return v___x_3586_;
}
else
{
lean_object* v_tail_3587_; 
v_tail_3587_ = lean_ctor_get(v_x_3584_, 1);
if (lean_obj_tag(v_tail_3587_) == 0)
{
lean_object* v_head_3588_; lean_object* v___x_3589_; 
lean_dec(v_x_3585_);
v_head_3588_ = lean_ctor_get(v_x_3584_, 0);
lean_inc(v_head_3588_);
lean_dec_ref(v_x_3584_);
v___x_3589_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3588_);
return v___x_3589_;
}
else
{
lean_object* v_head_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
lean_inc(v_tail_3587_);
v_head_3590_ = lean_ctor_get(v_x_3584_, 0);
lean_inc(v_head_3590_);
lean_dec_ref(v_x_3584_);
v___x_3591_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3590_);
v___x_3592_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3585_, v___x_3591_, v_tail_3587_);
return v___x_3592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3593_){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v___x_3594_ = lean_array_get_size(v_xs_3593_);
v___x_3595_ = lean_unsigned_to_nat(0u);
v___x_3596_ = lean_nat_dec_eq(v___x_3594_, v___x_3595_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3597_ = lean_array_to_list(v_xs_3593_);
v___x_3598_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3599_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3597_, v___x_3598_);
v___x_3600_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3601_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
lean_ctor_set(v___x_3602_, 1, v___x_3599_);
v___x_3603_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3602_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3600_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = l_Std_Format_fill(v___x_3605_);
return v___x_3606_;
}
else
{
lean_object* v___x_3607_; 
lean_dec_ref(v_xs_3593_);
v___x_3607_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3607_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3608_, lean_object* v_x_3609_, lean_object* v_x_3610_){
_start:
{
if (lean_obj_tag(v_x_3610_) == 0)
{
lean_dec(v_x_3608_);
return v_x_3609_;
}
else
{
lean_object* v_head_3611_; lean_object* v_tail_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3623_; 
v_head_3611_ = lean_ctor_get(v_x_3610_, 0);
v_tail_3612_ = lean_ctor_get(v_x_3610_, 1);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_x_3610_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3614_ = v_x_3610_;
v_isShared_3615_ = v_isSharedCheck_3623_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_tail_3612_);
lean_inc(v_head_3611_);
lean_dec(v_x_3610_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3623_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
lean_inc(v_x_3608_);
if (v_isShared_3615_ == 0)
{
lean_ctor_set_tag(v___x_3614_, 5);
lean_ctor_set(v___x_3614_, 1, v_x_3608_);
lean_ctor_set(v___x_3614_, 0, v_x_3609_);
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_x_3609_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_x_3608_);
v___x_3617_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3618_ = l_Nat_reprFast(v_head_3611_);
v___x_3619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
v___x_3620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3617_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v_x_3609_ = v___x_3620_;
v_x_3610_ = v_tail_3612_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3624_, lean_object* v_x_3625_, lean_object* v_x_3626_){
_start:
{
if (lean_obj_tag(v_x_3626_) == 0)
{
lean_dec(v_x_3624_);
return v_x_3625_;
}
else
{
lean_object* v_head_3627_; lean_object* v_tail_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3639_; 
v_head_3627_ = lean_ctor_get(v_x_3626_, 0);
v_tail_3628_ = lean_ctor_get(v_x_3626_, 1);
v_isSharedCheck_3639_ = !lean_is_exclusive(v_x_3626_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3630_ = v_x_3626_;
v_isShared_3631_ = v_isSharedCheck_3639_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_tail_3628_);
lean_inc(v_head_3627_);
lean_dec(v_x_3626_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3639_;
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
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_x_3625_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v_x_3624_);
v___x_3633_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3634_ = l_Nat_reprFast(v_head_3627_);
v___x_3635_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
v___x_3636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3633_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
v___x_3637_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3624_, v___x_3636_, v_tail_3628_);
return v___x_3637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = l_Nat_reprFast(v___y_3640_);
v___x_3642_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3643_, lean_object* v_x_3644_){
_start:
{
if (lean_obj_tag(v_x_3643_) == 0)
{
lean_object* v___x_3645_; 
lean_dec(v_x_3644_);
v___x_3645_ = lean_box(0);
return v___x_3645_;
}
else
{
lean_object* v_tail_3646_; 
v_tail_3646_ = lean_ctor_get(v_x_3643_, 1);
if (lean_obj_tag(v_tail_3646_) == 0)
{
lean_object* v_head_3647_; lean_object* v___x_3648_; 
lean_dec(v_x_3644_);
v_head_3647_ = lean_ctor_get(v_x_3643_, 0);
lean_inc(v_head_3647_);
lean_dec_ref(v_x_3643_);
v___x_3648_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3647_);
return v___x_3648_;
}
else
{
lean_object* v_head_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_inc(v_tail_3646_);
v_head_3649_ = lean_ctor_get(v_x_3643_, 0);
lean_inc(v_head_3649_);
lean_dec_ref(v_x_3643_);
v___x_3650_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3649_);
v___x_3651_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3644_, v___x_3650_, v_tail_3646_);
return v___x_3651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3652_){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; 
v___x_3653_ = lean_array_get_size(v_xs_3652_);
v___x_3654_ = lean_unsigned_to_nat(0u);
v___x_3655_ = lean_nat_dec_eq(v___x_3653_, v___x_3654_);
if (v___x_3655_ == 0)
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3656_ = lean_array_to_list(v_xs_3652_);
v___x_3657_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3658_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3656_, v___x_3657_);
v___x_3659_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3660_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set(v___x_3661_, 1, v___x_3658_);
v___x_3662_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3659_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = l_Std_Format_fill(v___x_3664_);
return v___x_3665_;
}
else
{
lean_object* v___x_3666_; 
lean_dec_ref(v_xs_3652_);
v___x_3666_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3666_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3667_, lean_object* v_x_3668_, lean_object* v_x_3669_){
_start:
{
if (lean_obj_tag(v_x_3669_) == 0)
{
lean_dec(v_x_3667_);
return v_x_3668_;
}
else
{
lean_object* v_head_3670_; lean_object* v_tail_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3681_; 
v_head_3670_ = lean_ctor_get(v_x_3669_, 0);
v_tail_3671_ = lean_ctor_get(v_x_3669_, 1);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_x_3669_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3673_ = v_x_3669_;
v_isShared_3674_ = v_isSharedCheck_3681_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_tail_3671_);
lean_inc(v_head_3670_);
lean_dec(v_x_3669_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3681_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
lean_inc(v_x_3667_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set_tag(v___x_3673_, 5);
lean_ctor_set(v___x_3673_, 1, v_x_3667_);
lean_ctor_set(v___x_3673_, 0, v_x_3668_);
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_x_3668_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_x_3667_);
v___x_3676_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3677_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3670_);
v___x_3678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3676_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
v_x_3668_ = v___x_3678_;
v_x_3669_ = v_tail_3671_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3682_, lean_object* v_x_3683_){
_start:
{
if (lean_obj_tag(v_x_3682_) == 0)
{
lean_object* v___x_3684_; 
lean_dec(v_x_3683_);
v___x_3684_ = lean_box(0);
return v___x_3684_;
}
else
{
lean_object* v_tail_3685_; 
v_tail_3685_ = lean_ctor_get(v_x_3682_, 1);
if (lean_obj_tag(v_tail_3685_) == 0)
{
lean_object* v_head_3686_; lean_object* v___x_3687_; 
lean_dec(v_x_3683_);
v_head_3686_ = lean_ctor_get(v_x_3682_, 0);
lean_inc(v_head_3686_);
lean_dec_ref(v_x_3682_);
v___x_3687_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3686_);
return v___x_3687_;
}
else
{
lean_object* v_head_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
lean_inc(v_tail_3685_);
v_head_3688_ = lean_ctor_get(v_x_3682_, 0);
lean_inc(v_head_3688_);
lean_dec_ref(v_x_3682_);
v___x_3689_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3688_);
v___x_3690_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3683_, v___x_3689_, v_tail_3685_);
return v___x_3690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3691_){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; uint8_t v___x_3694_; 
v___x_3692_ = lean_array_get_size(v_xs_3691_);
v___x_3693_ = lean_unsigned_to_nat(0u);
v___x_3694_ = lean_nat_dec_eq(v___x_3692_, v___x_3693_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3695_ = lean_array_to_list(v_xs_3691_);
v___x_3696_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3697_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3695_, v___x_3696_);
v___x_3698_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3699_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
lean_ctor_set(v___x_3700_, 1, v___x_3697_);
v___x_3701_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3700_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
v___x_3703_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3698_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = l_Std_Format_fill(v___x_3703_);
return v___x_3704_;
}
else
{
lean_object* v___x_3705_; 
lean_dec_ref(v_xs_3691_);
v___x_3705_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3705_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3706_, lean_object* v_x_3707_, lean_object* v_x_3708_){
_start:
{
if (lean_obj_tag(v_x_3708_) == 0)
{
lean_dec(v_x_3706_);
return v_x_3707_;
}
else
{
lean_object* v_head_3709_; lean_object* v_tail_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3720_; 
v_head_3709_ = lean_ctor_get(v_x_3708_, 0);
v_tail_3710_ = lean_ctor_get(v_x_3708_, 1);
v_isSharedCheck_3720_ = !lean_is_exclusive(v_x_3708_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3712_ = v_x_3708_;
v_isShared_3713_ = v_isSharedCheck_3720_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_tail_3710_);
lean_inc(v_head_3709_);
lean_dec(v_x_3708_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3720_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
lean_inc(v_x_3706_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set_tag(v___x_3712_, 5);
lean_ctor_set(v___x_3712_, 1, v_x_3706_);
lean_ctor_set(v___x_3712_, 0, v_x_3707_);
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_x_3707_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_x_3706_);
v___x_3715_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3709_);
v___x_3717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v_x_3707_ = v___x_3717_;
v_x_3708_ = v_tail_3710_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3721_, lean_object* v_x_3722_){
_start:
{
if (lean_obj_tag(v_x_3721_) == 0)
{
lean_object* v___x_3723_; 
lean_dec(v_x_3722_);
v___x_3723_ = lean_box(0);
return v___x_3723_;
}
else
{
lean_object* v_tail_3724_; 
v_tail_3724_ = lean_ctor_get(v_x_3721_, 1);
if (lean_obj_tag(v_tail_3724_) == 0)
{
lean_object* v_head_3725_; lean_object* v___x_3726_; 
lean_dec(v_x_3722_);
v_head_3725_ = lean_ctor_get(v_x_3721_, 0);
lean_inc(v_head_3725_);
lean_dec_ref(v_x_3721_);
v___x_3726_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3725_);
return v___x_3726_;
}
else
{
lean_object* v_head_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
lean_inc(v_tail_3724_);
v_head_3727_ = lean_ctor_get(v_x_3721_, 0);
lean_inc(v_head_3727_);
lean_dec_ref(v_x_3721_);
v___x_3728_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3727_);
v___x_3729_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3722_, v___x_3728_, v_tail_3724_);
return v___x_3729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3730_){
_start:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; uint8_t v___x_3733_; 
v___x_3731_ = lean_array_get_size(v_xs_3730_);
v___x_3732_ = lean_unsigned_to_nat(0u);
v___x_3733_ = lean_nat_dec_eq(v___x_3731_, v___x_3732_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3734_ = lean_array_to_list(v_xs_3730_);
v___x_3735_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3736_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3734_, v___x_3735_);
v___x_3737_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3738_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
lean_ctor_set(v___x_3739_, 1, v___x_3736_);
v___x_3740_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3737_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
v___x_3743_ = l_Std_Format_fill(v___x_3742_);
return v___x_3743_;
}
else
{
lean_object* v___x_3744_; 
lean_dec_ref(v_xs_3730_);
v___x_3744_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3744_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3758_ = lean_unsigned_to_nat(12u);
v___x_3759_ = lean_nat_to_int(v___x_3758_);
return v___x_3759_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = lean_unsigned_to_nat(9u);
v___x_3764_ = lean_nat_to_int(v___x_3763_);
return v___x_3764_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3768_ = lean_unsigned_to_nat(11u);
v___x_3769_ = lean_nat_to_int(v___x_3768_);
return v___x_3769_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3772_ = lean_string_length(v___x_3771_);
return v___x_3772_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3774_ = lean_nat_to_int(v___x_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3779_){
_start:
{
lean_object* v_numFixed_3780_; lean_object* v_perms_3781_; lean_object* v_revDeps_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v_numFixed_3780_ = lean_ctor_get(v_x_3779_, 0);
lean_inc(v_numFixed_3780_);
v_perms_3781_ = lean_ctor_get(v_x_3779_, 1);
lean_inc_ref(v_perms_3781_);
v_revDeps_3782_ = lean_ctor_get(v_x_3779_, 2);
lean_inc_ref(v_revDeps_3782_);
lean_dec_ref(v_x_3779_);
v___x_3783_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3784_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3785_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3786_ = l_Nat_reprFast(v_numFixed_3780_);
v___x_3787_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3786_);
v___x_3788_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3785_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
v___x_3789_ = 0;
v___x_3790_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3790_, 0, v___x_3788_);
lean_ctor_set_uint8(v___x_3790_, sizeof(void*)*1, v___x_3789_);
v___x_3791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3784_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3791_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
v___x_3794_ = lean_box(1);
v___x_3795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3793_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3795_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
lean_ctor_set(v___x_3798_, 1, v___x_3783_);
v___x_3799_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3800_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3781_);
v___x_3801_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3799_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
lean_ctor_set_uint8(v___x_3802_, sizeof(void*)*1, v___x_3789_);
v___x_3803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3798_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
lean_ctor_set(v___x_3804_, 1, v___x_3792_);
v___x_3805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3804_);
lean_ctor_set(v___x_3805_, 1, v___x_3794_);
v___x_3806_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3805_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
lean_ctor_set(v___x_3808_, 1, v___x_3783_);
v___x_3809_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3810_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3782_);
v___x_3811_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
lean_ctor_set_uint8(v___x_3812_, sizeof(void*)*1, v___x_3789_);
v___x_3813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3808_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3815_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
lean_ctor_set(v___x_3816_, 1, v___x_3813_);
v___x_3817_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3814_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
v___x_3820_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
lean_ctor_set_uint8(v___x_3820_, sizeof(void*)*1, v___x_3789_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3821_, lean_object* v_prec_3822_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3821_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3824_, lean_object* v_prec_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3824_, v_prec_3825_);
lean_dec(v_prec_3825_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v___f_3835_; lean_object* v___x_6079__overap_3836_; lean_object* v___x_3837_; 
v___f_3835_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_6079__overap_3836_ = lean_panic_fn(v___f_3835_, v_msg_3829_);
v___x_3837_ = lean_apply_5(v___x_6079__overap_3836_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, lean_box(0));
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___f_3851_; lean_object* v___x_6089__overap_3852_; lean_object* v___x_3853_; 
v___f_3851_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_6089__overap_3852_ = lean_panic_fn(v___f_3851_, v_msg_3845_);
v___x_3853_ = lean_apply_5(v___x_6089__overap_3852_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, lean_box(0));
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___f_3867_; lean_object* v___x_6099__overap_3868_; lean_object* v___x_3869_; 
v___f_3867_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_6099__overap_3868_ = lean_panic_fn(v___f_3867_, v_msg_3861_);
v___x_3869_ = lean_apply_5(v___x_6099__overap_3868_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, lean_box(0));
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v_res_3876_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3880_ = lean_unsigned_to_nat(12u);
v___x_3881_ = lean_unsigned_to_nat(294u);
v___x_3882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3883_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3884_ = l_mkPanicMessageWithDecl(v___x_3883_, v___x_3882_, v___x_3881_, v___x_3880_, v___x_3879_);
return v___x_3884_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3887_ = lean_unsigned_to_nat(12u);
v___x_3888_ = lean_unsigned_to_nat(297u);
v___x_3889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3890_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3891_ = l_mkPanicMessageWithDecl(v___x_3890_, v___x_3889_, v___x_3888_, v___x_3887_, v___x_3886_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3892_, lean_object* v_as_3893_, size_t v_sz_3894_, size_t v_i_3895_, lean_object* v_b_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v_a_3903_; uint8_t v___x_3907_; 
v___x_3907_ = lean_usize_dec_lt(v_i_3895_, v_sz_3894_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; 
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
v___x_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3908_, 0, v_b_3896_);
return v___x_3908_;
}
else
{
lean_object* v_a_3909_; 
v_a_3909_ = lean_array_uget_borrowed(v_as_3893_, v_i_3895_);
if (lean_obj_tag(v_a_3909_) == 1)
{
lean_object* v_val_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v_val_3910_ = lean_ctor_get(v_a_3909_, 0);
v___x_3911_ = lean_unsigned_to_nat(0u);
v___x_3912_ = lean_box(0);
v___x_3913_ = lean_array_get_borrowed(v___x_3912_, v_val_3910_, v___x_3911_);
if (lean_obj_tag(v___x_3913_) == 1)
{
lean_object* v_val_3914_; lean_object* v___x_3915_; 
v_val_3914_ = lean_ctor_get(v___x_3913_, 0);
v___x_3915_ = lean_array_get_borrowed(v___x_3912_, v___x_3892_, v_val_3914_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v___x_3916_; lean_object* v___x_3917_; 
lean_dec_ref(v_b_3896_);
v___x_3916_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
lean_inc(v___y_3900_);
lean_inc_ref(v___y_3899_);
lean_inc(v___y_3898_);
lean_inc_ref(v___y_3897_);
v___x_3917_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3916_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3927_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3920_ = v___x_3917_;
v_isShared_3921_ = v_isSharedCheck_3927_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3927_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
if (lean_obj_tag(v_a_3918_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3924_; 
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
v_a_3922_ = lean_ctor_get(v_a_3918_, 0);
lean_inc(v_a_3922_);
lean_dec_ref(v_a_3918_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 0, v_a_3922_);
v___x_3924_ = v___x_3920_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3922_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
else
{
lean_object* v_a_3926_; 
lean_del_object(v___x_3920_);
v_a_3926_ = lean_ctor_get(v_a_3918_, 0);
lean_inc(v_a_3926_);
lean_dec_ref(v_a_3918_);
v_a_3903_ = v_a_3926_;
goto v___jp_3902_;
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
v_a_3928_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3917_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3917_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
else
{
lean_object* v___x_3936_; 
lean_inc_ref(v___x_3915_);
v___x_3936_ = lean_array_push(v_b_3896_, v___x_3915_);
v_a_3903_ = v___x_3936_;
goto v___jp_3902_;
}
}
else
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
lean_inc(v___y_3900_);
lean_inc_ref(v___y_3899_);
lean_inc(v___y_3898_);
lean_inc_ref(v___y_3897_);
v___x_3938_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3937_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_dec_ref(v___x_3938_);
v_a_3903_ = v_b_3896_;
goto v___jp_3902_;
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec_ref(v_b_3896_);
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3938_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3938_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
}
else
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = lean_box(0);
v___x_3948_ = lean_array_push(v_b_3896_, v___x_3947_);
v_a_3903_ = v___x_3948_;
goto v___jp_3902_;
}
}
v___jp_3902_:
{
size_t v___x_3904_; size_t v___x_3905_; 
v___x_3904_ = ((size_t)1ULL);
v___x_3905_ = lean_usize_add(v_i_3895_, v___x_3904_);
v_i_3895_ = v___x_3905_;
v_b_3896_ = v_a_3903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3949_, lean_object* v_as_3950_, lean_object* v_sz_3951_, lean_object* v_i_3952_, lean_object* v_b_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
size_t v_sz_boxed_3959_; size_t v_i_boxed_3960_; lean_object* v_res_3961_; 
v_sz_boxed_3959_ = lean_unbox_usize(v_sz_3951_);
lean_dec(v_sz_3951_);
v_i_boxed_3960_ = lean_unbox_usize(v_i_3952_);
lean_dec(v_i_3952_);
v_res_3961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3949_, v_as_3950_, v_sz_boxed_3959_, v_i_boxed_3960_, v_b_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
lean_dec_ref(v_as_3950_);
lean_dec_ref(v___x_3949_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3964_, lean_object* v___x_3965_, lean_object* v___x_3966_, lean_object* v_a_3967_, lean_object* v_b_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
uint8_t v___x_3974_; 
v___x_3974_ = lean_nat_dec_lt(v_a_3967_, v_upperBound_3964_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; 
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v_a_3967_);
v___x_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3975_, 0, v_b_3968_);
return v___x_3975_;
}
else
{
lean_object* v___x_3976_; lean_object* v___x_3977_; size_t v_sz_3978_; size_t v___x_3979_; lean_object* v___x_3980_; 
v___x_3976_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3977_ = lean_array_fget_borrowed(v___x_3965_, v_a_3967_);
v_sz_3978_ = lean_array_size(v___x_3977_);
v___x_3979_ = ((size_t)0ULL);
lean_inc(v___y_3972_);
lean_inc_ref(v___y_3971_);
lean_inc(v___y_3970_);
lean_inc_ref(v___y_3969_);
v___x_3980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3966_, v___x_3977_, v_sz_3978_, v___x_3979_, v___x_3976_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3981_);
lean_dec_ref(v___x_3980_);
v___x_3982_ = lean_array_push(v_b_3968_, v_a_3981_);
v___x_3983_ = lean_unsigned_to_nat(1u);
v___x_3984_ = lean_nat_add(v_a_3967_, v___x_3983_);
lean_dec(v_a_3967_);
v_a_3967_ = v___x_3984_;
v_b_3968_ = v___x_3982_;
goto _start;
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec_ref(v_b_3968_);
lean_dec(v_a_3967_);
v_a_3986_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3980_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3980_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3994_, lean_object* v___x_3995_, lean_object* v___x_3996_, lean_object* v_a_3997_, lean_object* v_b_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3994_, v___x_3995_, v___x_3996_, v_a_3997_, v_b_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
lean_dec_ref(v___x_3996_);
lean_dec_ref(v___x_3995_);
lean_dec(v_upperBound_3994_);
return v_res_4004_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4006_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_4007_ = lean_unsigned_to_nat(8u);
v___x_4008_ = lean_unsigned_to_nat(281u);
v___x_4009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4010_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4011_ = l_mkPanicMessageWithDecl(v___x_4010_, v___x_4009_, v___x_4008_, v___x_4007_, v___x_4006_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_4012_, lean_object* v_a_4013_, lean_object* v_b_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v_a_4021_; uint8_t v___x_4025_; 
v___x_4025_ = lean_nat_dec_lt(v_a_4013_, v_upperBound_4012_);
if (v___x_4025_ == 0)
{
lean_object* v___x_4026_; 
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v_a_4013_);
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v_b_4014_);
return v___x_4026_;
}
else
{
lean_object* v_snd_4027_; lean_object* v_snd_4028_; lean_object* v_snd_4029_; lean_object* v_fst_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4154_; 
v_snd_4027_ = lean_ctor_get(v_b_4014_, 1);
lean_inc(v_snd_4027_);
v_snd_4028_ = lean_ctor_get(v_snd_4027_, 1);
lean_inc(v_snd_4028_);
v_snd_4029_ = lean_ctor_get(v_snd_4028_, 1);
lean_inc(v_snd_4029_);
v_fst_4030_ = lean_ctor_get(v_b_4014_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v_b_4014_);
if (v_isSharedCheck_4154_ == 0)
{
lean_object* v_unused_4155_; 
v_unused_4155_ = lean_ctor_get(v_b_4014_, 1);
lean_dec(v_unused_4155_);
v___x_4032_ = v_b_4014_;
v_isShared_4033_ = v_isSharedCheck_4154_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_fst_4030_);
lean_dec(v_b_4014_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4154_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v_fst_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4152_; 
v_fst_4034_ = lean_ctor_get(v_snd_4027_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v_snd_4027_);
if (v_isSharedCheck_4152_ == 0)
{
lean_object* v_unused_4153_; 
v_unused_4153_ = lean_ctor_get(v_snd_4027_, 1);
lean_dec(v_unused_4153_);
v___x_4036_ = v_snd_4027_;
v_isShared_4037_ = v_isSharedCheck_4152_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_fst_4034_);
lean_dec(v_snd_4027_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4152_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v_fst_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4150_; 
v_fst_4038_ = lean_ctor_get(v_snd_4028_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v_snd_4028_);
if (v_isSharedCheck_4150_ == 0)
{
lean_object* v_unused_4151_; 
v_unused_4151_ = lean_ctor_get(v_snd_4028_, 1);
lean_dec(v_unused_4151_);
v___x_4040_ = v_snd_4028_;
v_isShared_4041_ = v_isSharedCheck_4150_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_fst_4038_);
lean_dec(v_snd_4028_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4150_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v_array_4042_; lean_object* v_start_4043_; lean_object* v_stop_4044_; uint8_t v___x_4045_; 
v_array_4042_ = lean_ctor_get(v_snd_4029_, 0);
v_start_4043_ = lean_ctor_get(v_snd_4029_, 1);
v_stop_4044_ = lean_ctor_get(v_snd_4029_, 2);
v___x_4045_ = lean_nat_dec_lt(v_start_4043_, v_stop_4044_);
if (v___x_4045_ == 0)
{
lean_object* v___x_4047_; 
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v_a_4013_);
if (v_isShared_4041_ == 0)
{
v___x_4047_ = v___x_4040_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_fst_4038_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v_snd_4029_);
v___x_4047_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
lean_object* v___x_4049_; 
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 1, v___x_4047_);
v___x_4049_ = v___x_4036_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_fst_4034_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v___x_4047_);
v___x_4049_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
lean_object* v___x_4051_; 
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 1, v___x_4049_);
v___x_4051_ = v___x_4032_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_fst_4030_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
lean_object* v___x_4052_; 
v___x_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
return v___x_4052_;
}
}
}
}
else
{
lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4146_; 
lean_inc(v_stop_4044_);
lean_inc(v_start_4043_);
lean_inc_ref(v_array_4042_);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_snd_4029_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; lean_object* v_unused_4148_; lean_object* v_unused_4149_; 
v_unused_4147_ = lean_ctor_get(v_snd_4029_, 2);
lean_dec(v_unused_4147_);
v_unused_4148_ = lean_ctor_get(v_snd_4029_, 1);
lean_dec(v_unused_4148_);
v_unused_4149_ = lean_ctor_get(v_snd_4029_, 0);
lean_dec(v_unused_4149_);
v___x_4057_ = v_snd_4029_;
v_isShared_4058_ = v_isSharedCheck_4146_;
goto v_resetjp_4056_;
}
else
{
lean_dec(v_snd_4029_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4146_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v_array_4059_; lean_object* v_start_4060_; lean_object* v_stop_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4066_; 
v_array_4059_ = lean_ctor_get(v_fst_4038_, 0);
v_start_4060_ = lean_ctor_get(v_fst_4038_, 1);
v_stop_4061_ = lean_ctor_get(v_fst_4038_, 2);
v___x_4062_ = lean_array_fget(v_array_4042_, v_start_4043_);
v___x_4063_ = lean_unsigned_to_nat(1u);
v___x_4064_ = lean_nat_add(v_start_4043_, v___x_4063_);
lean_dec(v_start_4043_);
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 1, v___x_4064_);
v___x_4066_ = v___x_4057_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_array_4042_);
lean_ctor_set(v_reuseFailAlloc_4145_, 1, v___x_4064_);
lean_ctor_set(v_reuseFailAlloc_4145_, 2, v_stop_4044_);
v___x_4066_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
uint8_t v___x_4067_; 
v___x_4067_ = lean_nat_dec_lt(v_start_4060_, v_stop_4061_);
if (v___x_4067_ == 0)
{
lean_object* v___x_4069_; 
lean_dec(v___x_4062_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v_a_4013_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 1, v___x_4066_);
v___x_4069_ = v___x_4040_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_fst_4038_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v___x_4066_);
v___x_4069_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4071_; 
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 1, v___x_4069_);
v___x_4071_ = v___x_4036_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_fst_4034_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v___x_4069_);
v___x_4071_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
lean_object* v___x_4073_; 
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 1, v___x_4071_);
v___x_4073_ = v___x_4032_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_fst_4030_);
lean_ctor_set(v_reuseFailAlloc_4075_, 1, v___x_4071_);
v___x_4073_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
return v___x_4074_;
}
}
}
}
else
{
lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4141_; 
lean_inc(v_stop_4061_);
lean_inc(v_start_4060_);
lean_inc_ref(v_array_4059_);
v_isSharedCheck_4141_ = !lean_is_exclusive(v_fst_4038_);
if (v_isSharedCheck_4141_ == 0)
{
lean_object* v_unused_4142_; lean_object* v_unused_4143_; lean_object* v_unused_4144_; 
v_unused_4142_ = lean_ctor_get(v_fst_4038_, 2);
lean_dec(v_unused_4142_);
v_unused_4143_ = lean_ctor_get(v_fst_4038_, 1);
lean_dec(v_unused_4143_);
v_unused_4144_ = lean_ctor_get(v_fst_4038_, 0);
lean_dec(v_unused_4144_);
v___x_4079_ = v_fst_4038_;
v_isShared_4080_ = v_isSharedCheck_4141_;
goto v_resetjp_4078_;
}
else
{
lean_dec(v_fst_4038_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4141_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4081_; lean_object* v___x_4083_; 
v___x_4081_ = lean_nat_add(v_start_4060_, v___x_4063_);
lean_dec(v_start_4060_);
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 1, v___x_4081_);
v___x_4083_ = v___x_4079_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_array_4059_);
lean_ctor_set(v_reuseFailAlloc_4140_, 1, v___x_4081_);
lean_ctor_set(v_reuseFailAlloc_4140_, 2, v_stop_4061_);
v___x_4083_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
if (lean_obj_tag(v___x_4062_) == 1)
{
lean_object* v_val_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4128_; 
v_val_4084_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4086_ = v___x_4062_;
v_isShared_4087_ = v_isSharedCheck_4128_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_val_4084_);
lean_dec(v___x_4062_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4128_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4093_; 
v___x_4088_ = lean_unsigned_to_nat(0u);
v___x_4089_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4090_ = lean_box(0);
v___x_4091_ = lean_array_get(v___x_4090_, v_val_4084_, v___x_4088_);
lean_dec(v_val_4084_);
lean_inc(v_a_4013_);
if (v_isShared_4087_ == 0)
{
lean_ctor_set(v___x_4086_, 0, v_a_4013_);
v___x_4093_ = v___x_4086_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4013_);
v___x_4093_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
uint8_t v___x_4094_; 
v___x_4094_ = l_Option_instDecidableEq___redArg(v___x_4089_, v___x_4091_, v___x_4093_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
lean_dec_ref(v___x_4083_);
lean_dec_ref(v___x_4066_);
lean_del_object(v___x_4040_);
lean_del_object(v___x_4036_);
lean_dec(v_fst_4034_);
lean_del_object(v___x_4032_);
lean_dec(v_fst_4030_);
v___x_4095_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
lean_inc(v___y_4018_);
lean_inc_ref(v___y_4017_);
lean_inc(v___y_4016_);
lean_inc_ref(v___y_4015_);
v___x_4096_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4095_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4106_; 
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4099_ = v___x_4096_;
v_isShared_4100_ = v_isSharedCheck_4106_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4096_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4106_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
if (lean_obj_tag(v_a_4097_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4103_; 
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v_a_4013_);
v_a_4101_ = lean_ctor_get(v_a_4097_, 0);
lean_inc(v_a_4101_);
lean_dec_ref(v_a_4097_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v_a_4101_);
v___x_4103_ = v___x_4099_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4101_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
else
{
lean_object* v_a_4105_; 
lean_del_object(v___x_4099_);
v_a_4105_ = lean_ctor_get(v_a_4097_, 0);
lean_inc(v_a_4105_);
lean_dec_ref(v_a_4097_);
v_a_4021_ = v_a_4105_;
goto v___jp_4020_;
}
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v_a_4013_);
v_a_4107_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4096_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4096_);
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
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4119_; 
lean_inc(v_fst_4034_);
v___x_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4115_, 0, v_fst_4034_);
v___x_4116_ = lean_array_push(v_fst_4030_, v___x_4115_);
v___x_4117_ = lean_nat_add(v_fst_4034_, v___x_4063_);
lean_dec(v_fst_4034_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 1, v___x_4066_);
lean_ctor_set(v___x_4040_, 0, v___x_4083_);
v___x_4119_ = v___x_4040_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v___x_4066_);
v___x_4119_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
lean_object* v___x_4121_; 
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 1, v___x_4119_);
lean_ctor_set(v___x_4036_, 0, v___x_4117_);
v___x_4121_ = v___x_4036_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4117_);
lean_ctor_set(v_reuseFailAlloc_4125_, 1, v___x_4119_);
v___x_4121_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
lean_object* v___x_4123_; 
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 1, v___x_4121_);
lean_ctor_set(v___x_4032_, 0, v___x_4116_);
v___x_4123_ = v___x_4032_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___x_4116_);
lean_ctor_set(v_reuseFailAlloc_4124_, 1, v___x_4121_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
v_a_4021_ = v___x_4123_;
goto v___jp_4020_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4132_; 
lean_dec(v___x_4062_);
v___x_4129_ = lean_box(0);
v___x_4130_ = lean_array_push(v_fst_4030_, v___x_4129_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 1, v___x_4066_);
lean_ctor_set(v___x_4040_, 0, v___x_4083_);
v___x_4132_ = v___x_4040_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v___x_4066_);
v___x_4132_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
lean_object* v___x_4134_; 
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 1, v___x_4132_);
v___x_4134_ = v___x_4036_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_fst_4034_);
lean_ctor_set(v_reuseFailAlloc_4138_, 1, v___x_4132_);
v___x_4134_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
lean_object* v___x_4136_; 
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 1, v___x_4134_);
lean_ctor_set(v___x_4032_, 0, v___x_4130_);
v___x_4136_ = v___x_4032_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4130_);
lean_ctor_set(v_reuseFailAlloc_4137_, 1, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
v_a_4021_ = v___x_4136_;
goto v___jp_4020_;
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
v___jp_4020_:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4022_ = lean_unsigned_to_nat(1u);
v___x_4023_ = lean_nat_add(v_a_4013_, v___x_4022_);
lean_dec(v_a_4013_);
v_a_4013_ = v___x_4023_;
v_b_4014_ = v_a_4021_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4156_, lean_object* v_a_4157_, lean_object* v_b_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4156_, v_a_4157_, v_b_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec(v_upperBound_4156_);
return v_res_4164_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4166_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4167_ = lean_unsigned_to_nat(4u);
v___x_4168_ = lean_unsigned_to_nat(275u);
v___x_4169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4170_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4171_ = l_mkPanicMessageWithDecl(v___x_4170_, v___x_4169_, v___x_4168_, v___x_4167_, v___x_4166_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4172_, lean_object* v___x_4173_, lean_object* v___x_4174_, lean_object* v_xs_4175_, lean_object* v_x_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_graph_4182_; lean_object* v_revDeps_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4236_; 
v_graph_4182_ = lean_ctor_get(v_a_4172_, 0);
v_revDeps_4183_ = lean_ctor_get(v_a_4172_, 1);
v_isSharedCheck_4236_ = !lean_is_exclusive(v_a_4172_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4185_ = v_a_4172_;
v_isShared_4186_ = v_isSharedCheck_4236_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_revDeps_4183_);
lean_inc(v_graph_4182_);
lean_dec(v_a_4172_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4236_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v___x_4187_ = lean_array_get_borrowed(v___x_4173_, v_graph_4182_, v___x_4174_);
v___x_4188_ = lean_array_get_size(v_xs_4175_);
v___x_4189_ = lean_array_get_size(v___x_4187_);
v___x_4190_ = lean_nat_dec_eq(v___x_4188_, v___x_4189_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
lean_del_object(v___x_4185_);
lean_dec_ref(v_revDeps_4183_);
lean_dec_ref(v_graph_4182_);
lean_dec_ref(v_xs_4175_);
lean_dec(v___x_4174_);
v___x_4191_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4192_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4191_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
return v___x_4192_;
}
else
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4197_; 
v___x_4193_ = lean_mk_empty_array_with_capacity(v___x_4174_);
lean_inc(v___x_4174_);
v___x_4194_ = l_Array_toSubarray___redArg(v_xs_4175_, v___x_4174_, v___x_4188_);
lean_inc(v___x_4174_);
lean_inc(v___x_4187_);
v___x_4195_ = l_Array_toSubarray___redArg(v___x_4187_, v___x_4174_, v___x_4189_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 1, v___x_4195_);
lean_ctor_set(v___x_4185_, 0, v___x_4194_);
v___x_4197_ = v___x_4185_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4194_);
lean_ctor_set(v_reuseFailAlloc_4235_, 1, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
lean_inc(v___x_4174_);
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4174_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4193_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
lean_inc(v___y_4180_);
lean_inc_ref(v___y_4179_);
lean_inc(v___y_4178_);
lean_inc_ref(v___y_4177_);
v___x_4200_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4188_, v___x_4174_, v___x_4199_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v_snd_4202_; lean_object* v_fst_4203_; lean_object* v_fst_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4201_);
lean_dec_ref(v___x_4200_);
v_snd_4202_ = lean_ctor_get(v_a_4201_, 1);
lean_inc(v_snd_4202_);
v_fst_4203_ = lean_ctor_get(v_a_4201_, 0);
lean_inc(v_fst_4203_);
lean_dec(v_a_4201_);
v_fst_4204_ = lean_ctor_get(v_snd_4202_, 0);
lean_inc(v_fst_4204_);
lean_dec(v_snd_4202_);
v___x_4205_ = lean_unsigned_to_nat(1u);
v___x_4206_ = lean_array_get_size(v_graph_4182_);
v___x_4207_ = lean_mk_empty_array_with_capacity(v___x_4205_);
lean_inc(v_fst_4203_);
v___x_4208_ = lean_array_push(v___x_4207_, v_fst_4203_);
v___x_4209_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4206_, v_graph_4182_, v_fst_4203_, v___x_4205_, v___x_4208_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
lean_dec(v_fst_4203_);
lean_dec_ref(v_graph_4182_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4218_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4212_ = v___x_4209_;
v_isShared_4213_ = v_isSharedCheck_4218_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4209_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4218_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4214_; lean_object* v___x_4216_; 
v___x_4214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4214_, 0, v_fst_4204_);
lean_ctor_set(v___x_4214_, 1, v_a_4210_);
lean_ctor_set(v___x_4214_, 2, v_revDeps_4183_);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 0, v___x_4214_);
v___x_4216_ = v___x_4212_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4214_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
lean_dec(v_fst_4204_);
lean_dec_ref(v_revDeps_4183_);
v_a_4219_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4209_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4209_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec_ref(v_revDeps_4183_);
lean_dec_ref(v_graph_4182_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
v_a_4227_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4200_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4200_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4237_, lean_object* v___x_4238_, lean_object* v___x_4239_, lean_object* v_xs_4240_, lean_object* v_x_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4237_, v___x_4238_, v___x_4239_, v_xs_4240_, v_x_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
lean_dec_ref(v_x_4241_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_){
_start:
{
lean_object* v___x_4254_; 
lean_inc(v_a_4252_);
lean_inc_ref(v_a_4251_);
lean_inc(v_a_4250_);
lean_inc_ref(v_a_4249_);
lean_inc_ref(v_preDefs_4248_);
v___x_4254_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_a_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v_value_4259_; lean_object* v___x_4260_; lean_object* v___f_4261_; uint8_t v___x_4262_; lean_object* v___x_4263_; 
v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4255_);
lean_dec_ref(v___x_4254_);
v___x_4256_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4257_ = lean_unsigned_to_nat(0u);
v___x_4258_ = lean_array_get(v___x_4256_, v_preDefs_4248_, v___x_4257_);
lean_dec_ref(v_preDefs_4248_);
v_value_4259_ = lean_ctor_get(v___x_4258_, 7);
lean_inc_ref(v_value_4259_);
lean_dec(v___x_4258_);
v___x_4260_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4261_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4261_, 0, v_a_4255_);
lean_closure_set(v___f_4261_, 1, v___x_4260_);
lean_closure_set(v___f_4261_, 2, v___x_4257_);
v___x_4262_ = 0;
v___x_4263_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4259_, v___f_4261_, v___x_4262_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
return v___x_4263_;
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_dec(v_a_4252_);
lean_dec_ref(v_a_4251_);
lean_dec(v_a_4250_);
lean_dec_ref(v_a_4249_);
lean_dec_ref(v_preDefs_4248_);
v_a_4264_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4254_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4254_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4279_, lean_object* v___x_4280_, lean_object* v___x_4281_, lean_object* v_inst_4282_, lean_object* v_R_4283_, lean_object* v_a_4284_, lean_object* v_b_4285_, lean_object* v_c_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4279_, v___x_4280_, v___x_4281_, v_a_4284_, v_b_4285_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4293_, lean_object* v___x_4294_, lean_object* v___x_4295_, lean_object* v_inst_4296_, lean_object* v_R_4297_, lean_object* v_a_4298_, lean_object* v_b_4299_, lean_object* v_c_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4293_, v___x_4294_, v___x_4295_, v_inst_4296_, v_R_4297_, v_a_4298_, v_b_4299_, v_c_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
lean_dec_ref(v___x_4295_);
lean_dec_ref(v___x_4294_);
lean_dec(v_upperBound_4293_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4307_, lean_object* v_inst_4308_, lean_object* v_R_4309_, lean_object* v_a_4310_, lean_object* v_b_4311_, lean_object* v_c_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4307_, v_a_4310_, v_b_4311_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4319_, lean_object* v_inst_4320_, lean_object* v_R_4321_, lean_object* v_a_4322_, lean_object* v_b_4323_, lean_object* v_c_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4319_, v_inst_4320_, v_R_4321_, v_a_4322_, v_b_4323_, v_c_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v_upperBound_4319_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4331_, size_t v_i_4332_, size_t v_stop_4333_, lean_object* v_b_4334_){
_start:
{
uint8_t v___x_4335_; 
v___x_4335_ = lean_usize_dec_eq(v_i_4332_, v_stop_4333_);
if (v___x_4335_ == 0)
{
size_t v___x_4336_; size_t v___x_4337_; lean_object* v___x_4338_; 
v___x_4336_ = ((size_t)1ULL);
v___x_4337_ = lean_usize_sub(v_i_4332_, v___x_4336_);
v___x_4338_ = lean_array_uget_borrowed(v_as_4331_, v___x_4337_);
if (lean_obj_tag(v___x_4338_) == 0)
{
v_i_4332_ = v___x_4337_;
goto _start;
}
else
{
lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4340_ = lean_unsigned_to_nat(1u);
v___x_4341_ = lean_nat_add(v_b_4334_, v___x_4340_);
lean_dec(v_b_4334_);
v_i_4332_ = v___x_4337_;
v_b_4334_ = v___x_4341_;
goto _start;
}
}
else
{
return v_b_4334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4343_, lean_object* v_i_4344_, lean_object* v_stop_4345_, lean_object* v_b_4346_){
_start:
{
size_t v_i_boxed_4347_; size_t v_stop_boxed_4348_; lean_object* v_res_4349_; 
v_i_boxed_4347_ = lean_unbox_usize(v_i_4344_);
lean_dec(v_i_4344_);
v_stop_boxed_4348_ = lean_unbox_usize(v_stop_4345_);
lean_dec(v_stop_4345_);
v_res_4349_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4343_, v_i_boxed_4347_, v_stop_boxed_4348_, v_b_4346_);
lean_dec_ref(v_as_4343_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4350_){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; 
v___x_4351_ = lean_unsigned_to_nat(0u);
v___x_4352_ = lean_array_get_size(v_perm_4350_);
v___x_4353_ = lean_nat_dec_lt(v___x_4351_, v___x_4352_);
if (v___x_4353_ == 0)
{
return v___x_4351_;
}
else
{
size_t v___x_4354_; size_t v___x_4355_; lean_object* v___x_4356_; 
v___x_4354_ = lean_usize_of_nat(v___x_4352_);
v___x_4355_ = ((size_t)0ULL);
v___x_4356_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4350_, v___x_4354_, v___x_4355_, v___x_4351_);
return v___x_4356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4357_);
lean_dec_ref(v_perm_4357_);
return v_res_4358_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4359_, lean_object* v_i_4360_){
_start:
{
lean_object* v___x_4361_; uint8_t v___x_4362_; 
v___x_4361_ = lean_array_get_size(v_perm_4359_);
v___x_4362_ = lean_nat_dec_lt(v_i_4360_, v___x_4361_);
if (v___x_4362_ == 0)
{
return v___x_4362_;
}
else
{
lean_object* v___x_4363_; 
v___x_4363_ = lean_array_fget_borrowed(v_perm_4359_, v_i_4360_);
if (lean_obj_tag(v___x_4363_) == 0)
{
uint8_t v___x_4364_; 
v___x_4364_ = 0;
return v___x_4364_;
}
else
{
return v___x_4362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4365_, lean_object* v_i_4366_){
_start:
{
uint8_t v_res_4367_; lean_object* v_r_4368_; 
v_res_4367_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4365_, v_i_4366_);
lean_dec(v_i_4366_);
lean_dec_ref(v_perm_4365_);
v_r_4368_ = lean_box(v_res_4367_);
return v_r_4368_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
lean_object* v___f_4375_; lean_object* v___x_1080__overap_4376_; lean_object* v___x_4377_; 
v___f_4375_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_1080__overap_4376_ = lean_panic_fn(v___f_4375_, v_msg_4369_);
v___x_4377_ = lean_apply_5(v___x_1080__overap_4376_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, lean_box(0));
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4385_, lean_object* v_msg_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4393_, lean_object* v_msg_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4393_, v_msg_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4401_, lean_object* v_maxFVars_x3f_4402_, lean_object* v_k_4403_, uint8_t v_cleanupAnnotations_4404_, uint8_t v_whnfType_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v___f_4411_; lean_object* v___x_4412_; 
v___f_4411_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4411_, 0, v_k_4403_);
v___x_4412_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4401_, v_maxFVars_x3f_4402_, v___f_4411_, v_cleanupAnnotations_4404_, v_whnfType_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4412_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4412_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
v_a_4421_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4412_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4412_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4429_, lean_object* v_maxFVars_x3f_4430_, lean_object* v_k_4431_, lean_object* v_cleanupAnnotations_4432_, lean_object* v_whnfType_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4439_; uint8_t v_whnfType_boxed_4440_; lean_object* v_res_4441_; 
v_cleanupAnnotations_boxed_4439_ = lean_unbox(v_cleanupAnnotations_4432_);
v_whnfType_boxed_4440_ = lean_unbox(v_whnfType_4433_);
v_res_4441_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4429_, v_maxFVars_x3f_4430_, v_k_4431_, v_cleanupAnnotations_boxed_4439_, v_whnfType_boxed_4440_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4442_, lean_object* v_type_4443_, lean_object* v_maxFVars_x3f_4444_, lean_object* v_k_4445_, uint8_t v_cleanupAnnotations_4446_, uint8_t v_whnfType_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4443_, v_maxFVars_x3f_4444_, v_k_4445_, v_cleanupAnnotations_4446_, v_whnfType_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4454_, lean_object* v_type_4455_, lean_object* v_maxFVars_x3f_4456_, lean_object* v_k_4457_, lean_object* v_cleanupAnnotations_4458_, lean_object* v_whnfType_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4465_; uint8_t v_whnfType_boxed_4466_; lean_object* v_res_4467_; 
v_cleanupAnnotations_boxed_4465_ = lean_unbox(v_cleanupAnnotations_4458_);
v_whnfType_boxed_4466_ = lean_unbox(v_whnfType_4459_);
v_res_4467_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4454_, v_type_4455_, v_maxFVars_x3f_4456_, v_k_4457_, v_cleanupAnnotations_boxed_4465_, v_whnfType_boxed_4466_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
return v_res_4467_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4470_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4471_ = lean_unsigned_to_nat(6u);
v___x_4472_ = lean_unsigned_to_nat(329u);
v___x_4473_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4474_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4475_ = l_mkPanicMessageWithDecl(v___x_4474_, v___x_4473_, v___x_4472_, v___x_4471_, v___x_4470_);
return v___x_4475_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4479_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4480_ = lean_unsigned_to_nat(8u);
v___x_4481_ = lean_unsigned_to_nat(322u);
v___x_4482_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4483_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4484_ = l_mkPanicMessageWithDecl(v___x_4483_, v___x_4482_, v___x_4481_, v___x_4480_, v___x_4479_);
return v___x_4484_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4486_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4487_ = lean_unsigned_to_nat(8u);
v___x_4488_ = lean_unsigned_to_nat(325u);
v___x_4489_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4490_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4491_ = l_mkPanicMessageWithDecl(v___x_4490_, v___x_4489_, v___x_4488_, v___x_4487_, v___x_4486_);
return v___x_4491_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4493_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4494_ = lean_unsigned_to_nat(8u);
v___x_4495_ = lean_unsigned_to_nat(324u);
v___x_4496_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4497_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4498_ = l_mkPanicMessageWithDecl(v___x_4497_, v___x_4496_, v___x_4495_, v___x_4494_, v___x_4493_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4499_, lean_object* v_xs_4500_, lean_object* v_val_4501_, lean_object* v_i_4502_, lean_object* v_perm_4503_, lean_object* v_k_4504_, lean_object* v_xs_x27_4505_, lean_object* v_type_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v___x_4512_; uint8_t v___x_4513_; 
v___x_4512_ = lean_array_get_size(v_xs_x27_4505_);
v___x_4513_ = lean_nat_dec_eq(v___x_4512_, v___x_4499_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
lean_dec_ref(v_type_4506_);
lean_dec_ref(v_k_4504_);
lean_dec_ref(v_perm_4503_);
lean_dec_ref(v_xs_4500_);
v___x_4514_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4515_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4514_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
return v___x_4515_;
}
else
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v_x_4518_; lean_object* v___x_4519_; 
v___x_4516_ = l_Lean_instInhabitedExpr;
v___x_4517_ = lean_unsigned_to_nat(0u);
v_x_4518_ = lean_array_get_borrowed(v___x_4516_, v_xs_x27_4505_, v___x_4517_);
lean_inc(v___y_4510_);
lean_inc_ref(v___y_4509_);
lean_inc(v___y_4508_);
lean_inc_ref(v___y_4507_);
lean_inc(v_x_4518_);
v___x_4519_ = lean_infer_type(v_x_4518_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; uint8_t v___x_4521_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4520_);
lean_dec_ref(v___x_4519_);
v___x_4521_ = l_Lean_Expr_hasLooseBVars(v_a_4520_);
lean_dec(v_a_4520_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; uint8_t v___x_4523_; 
v___x_4522_ = lean_array_get_size(v_xs_4500_);
v___x_4523_ = lean_nat_dec_lt(v_val_4501_, v___x_4522_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
lean_dec_ref(v_type_4506_);
lean_dec_ref(v_k_4504_);
lean_dec_ref(v_perm_4503_);
lean_dec_ref(v_xs_4500_);
v___x_4524_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4525_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4524_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
return v___x_4525_;
}
else
{
lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4526_ = lean_nat_add(v_i_4502_, v___x_4499_);
lean_inc(v_x_4518_);
v___x_4527_ = lean_array_set(v_xs_4500_, v_val_4501_, v_x_4518_);
v___x_4528_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4503_, v_k_4504_, v___x_4526_, v_type_4506_, v___x_4527_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
return v___x_4528_;
}
}
else
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
lean_dec_ref(v_type_4506_);
lean_dec_ref(v_k_4504_);
lean_dec_ref(v_perm_4503_);
lean_dec_ref(v_xs_4500_);
v___x_4529_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4530_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4529_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
return v___x_4530_;
}
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec_ref(v_type_4506_);
lean_dec_ref(v_k_4504_);
lean_dec_ref(v_perm_4503_);
lean_dec_ref(v_xs_4500_);
v_a_4531_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4519_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4519_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4534_ == 0)
{
v___x_4536_ = v___x_4533_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4539_, lean_object* v_xs_4540_, lean_object* v_val_4541_, lean_object* v_i_4542_, lean_object* v_perm_4543_, lean_object* v_k_4544_, lean_object* v_xs_x27_4545_, lean_object* v_type_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4539_, v_xs_4540_, v_val_4541_, v_i_4542_, v_perm_4543_, v_k_4544_, v_xs_x27_4545_, v_type_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
lean_dec_ref(v_xs_x27_4545_);
lean_dec(v_i_4542_);
lean_dec(v_val_4541_);
lean_dec(v___x_4539_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4553_, lean_object* v_k_4554_, lean_object* v_i_4555_, lean_object* v_type_4556_, lean_object* v_xs_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_){
_start:
{
lean_object* v___x_4563_; uint8_t v___x_4564_; 
v___x_4563_ = lean_array_get_size(v_perm_4553_);
v___x_4564_ = lean_nat_dec_lt(v_i_4555_, v___x_4563_);
if (v___x_4564_ == 0)
{
lean_object* v___x_4565_; 
lean_dec_ref(v_type_4556_);
lean_dec(v_i_4555_);
lean_dec_ref(v_perm_4553_);
v___x_4565_ = lean_apply_6(v_k_4554_, v_xs_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, lean_box(0));
return v___x_4565_;
}
else
{
lean_object* v___x_4566_; 
v___x_4566_ = lean_array_fget_borrowed(v_perm_4553_, v_i_4555_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v___x_4567_; 
lean_inc(v_a_4561_);
lean_inc_ref(v_a_4560_);
lean_inc(v_a_4559_);
lean_inc_ref(v_a_4558_);
v___x_4567_ = lean_whnf(v_type_4556_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_object* v_a_4568_; uint8_t v___x_4569_; 
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc(v_a_4568_);
lean_dec_ref(v___x_4567_);
v___x_4569_ = l_Lean_Expr_isForall(v_a_4568_);
if (v___x_4569_ == 0)
{
lean_object* v___x_4570_; lean_object* v___x_4571_; 
lean_dec(v_a_4568_);
lean_dec_ref(v_xs_4557_);
lean_dec(v_i_4555_);
lean_dec_ref(v_k_4554_);
lean_dec_ref(v_perm_4553_);
v___x_4570_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4571_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4570_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
return v___x_4571_;
}
else
{
lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4572_ = lean_unsigned_to_nat(1u);
v___x_4573_ = lean_nat_add(v_i_4555_, v___x_4572_);
lean_dec(v_i_4555_);
v___x_4574_ = l_Lean_Expr_bindingBody_x21(v_a_4568_);
lean_dec(v_a_4568_);
v_i_4555_ = v___x_4573_;
v_type_4556_ = v___x_4574_;
goto _start;
}
}
else
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4583_; 
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v_a_4559_);
lean_dec_ref(v_a_4558_);
lean_dec_ref(v_xs_4557_);
lean_dec(v_i_4555_);
lean_dec_ref(v_k_4554_);
lean_dec_ref(v_perm_4553_);
v_a_4576_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4578_ = v___x_4567_;
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___x_4567_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4581_; 
if (v_isShared_4579_ == 0)
{
v___x_4581_ = v___x_4578_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
}
else
{
lean_object* v_val_4584_; lean_object* v___x_4585_; lean_object* v___f_4586_; lean_object* v___x_4587_; uint8_t v___x_4588_; lean_object* v___x_4589_; 
v_val_4584_ = lean_ctor_get(v___x_4566_, 0);
lean_inc(v_val_4584_);
v___x_4585_ = lean_unsigned_to_nat(1u);
v___f_4586_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4586_, 0, v___x_4585_);
lean_closure_set(v___f_4586_, 1, v_xs_4557_);
lean_closure_set(v___f_4586_, 2, v_val_4584_);
lean_closure_set(v___f_4586_, 3, v_i_4555_);
lean_closure_set(v___f_4586_, 4, v_perm_4553_);
lean_closure_set(v___f_4586_, 5, v_k_4554_);
v___x_4587_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4588_ = 0;
v___x_4589_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4556_, v___x_4587_, v___f_4586_, v___x_4564_, v___x_4588_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
return v___x_4589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4590_, lean_object* v_k_4591_, lean_object* v_i_4592_, lean_object* v_type_4593_, lean_object* v_xs_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_){
_start:
{
lean_object* v_res_4600_; 
v_res_4600_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4590_, v_k_4591_, v_i_4592_, v_type_4593_, v_xs_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_);
return v_res_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4601_, lean_object* v_perm_4602_, lean_object* v_k_4603_, lean_object* v_i_4604_, lean_object* v_type_4605_, lean_object* v_xs_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_){
_start:
{
lean_object* v___x_4612_; 
v___x_4612_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4602_, v_k_4603_, v_i_4604_, v_type_4605_, v_xs_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_);
return v___x_4612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4613_, lean_object* v_perm_4614_, lean_object* v_k_4615_, lean_object* v_i_4616_, lean_object* v_type_4617_, lean_object* v_xs_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
lean_object* v_res_4624_; 
v_res_4624_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4613_, v_perm_4614_, v_k_4615_, v_i_4616_, v_type_4617_, v_xs_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_);
return v_res_4624_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4625_ = lean_unsigned_to_nat(0u);
v___x_4626_ = l_Lean_Level_ofNat(v___x_4625_);
return v___x_4626_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4627_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4628_ = l_Lean_mkSort(v___x_4627_);
return v___x_4628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4629_, lean_object* v_type_4630_, lean_object* v_k_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4637_ = lean_unsigned_to_nat(0u);
v___x_4638_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4629_);
v___x_4639_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4640_ = lean_mk_array(v___x_4638_, v___x_4639_);
v___x_4641_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4629_, v_k_4631_, v___x_4637_, v_type_4630_, v___x_4640_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4642_, lean_object* v_type_4643_, lean_object* v_k_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4642_, v_type_4643_, v_k_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4651_, lean_object* v_perm_4652_, lean_object* v_type_4653_, lean_object* v_k_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
lean_object* v___x_4660_; 
v___x_4660_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4652_, v_type_4653_, v_k_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4661_, lean_object* v_perm_4662_, lean_object* v_type_4663_, lean_object* v_k_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_){
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4661_, v_perm_4662_, v_type_4663_, v_k_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_);
return v_res_4670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4671_, lean_object* v_runInBase_4672_, lean_object* v_b_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_){
_start:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4679_ = lean_apply_1(v_k_4671_, v_b_4673_);
v___x_4680_ = lean_apply_7(v_runInBase_4672_, lean_box(0), v___x_4679_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_, lean_box(0));
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4681_, lean_object* v_runInBase_4682_, lean_object* v_b_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4681_, v_runInBase_4682_, v_b_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4690_, lean_object* v_perm_4691_, lean_object* v_type_4692_, lean_object* v_runInBase_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
lean_object* v___f_4699_; lean_object* v___x_4700_; 
v___f_4699_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4699_, 0, v_k_4690_);
lean_closure_set(v___f_4699_, 1, v_runInBase_4693_);
v___x_4700_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4691_, v_type_4692_, v___f_4699_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
return v___x_4700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4701_, lean_object* v_perm_4702_, lean_object* v_type_4703_, lean_object* v_runInBase_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4701_, v_perm_4702_, v_type_4703_, v_runInBase_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4711_, lean_object* v_inst_4712_, lean_object* v_perm_4713_, lean_object* v_type_4714_, lean_object* v_k_4715_){
_start:
{
lean_object* v_toBind_4716_; lean_object* v_liftWith_4717_; lean_object* v_restoreM_4718_; lean_object* v___f_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v_toBind_4716_ = lean_ctor_get(v_inst_4712_, 1);
lean_inc(v_toBind_4716_);
lean_dec_ref(v_inst_4712_);
v_liftWith_4717_ = lean_ctor_get(v_inst_4711_, 0);
lean_inc(v_liftWith_4717_);
v_restoreM_4718_ = lean_ctor_get(v_inst_4711_, 1);
lean_inc(v_restoreM_4718_);
lean_dec_ref(v_inst_4711_);
v___f_4719_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4719_, 0, v_k_4715_);
lean_closure_set(v___f_4719_, 1, v_perm_4713_);
lean_closure_set(v___f_4719_, 2, v_type_4714_);
v___x_4720_ = lean_apply_2(v_liftWith_4717_, lean_box(0), v___f_4719_);
v___x_4721_ = lean_apply_1(v_restoreM_4718_, lean_box(0));
v___x_4722_ = lean_apply_4(v_toBind_4716_, lean_box(0), lean_box(0), v___x_4720_, v___x_4721_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4723_, lean_object* v_00_u03b1_4724_, lean_object* v_inst_4725_, lean_object* v_inst_4726_, lean_object* v_perm_4727_, lean_object* v_type_4728_, lean_object* v_k_4729_){
_start:
{
lean_object* v___x_4730_; 
v___x_4730_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4725_, v_inst_4726_, v_perm_4727_, v_type_4728_, v_k_4729_);
return v___x_4730_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
lean_object* v___f_4737_; lean_object* v___x_638__overap_4738_; lean_object* v___x_4739_; 
v___f_4737_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_638__overap_4738_ = lean_panic_fn(v___f_4737_, v_msg_4731_);
v___x_4739_ = lean_apply_5(v___x_638__overap_4738_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, lean_box(0));
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_){
_start:
{
lean_object* v_res_4746_; 
v_res_4746_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_);
return v_res_4746_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4749_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4750_ = lean_unsigned_to_nat(10u);
v___x_4751_ = lean_unsigned_to_nat(353u);
v___x_4752_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4753_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4754_ = l_mkPanicMessageWithDecl(v___x_4753_, v___x_4752_, v___x_4751_, v___x_4750_, v___x_4749_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4755_, lean_object* v_xs_4756_, lean_object* v_tail_4757_, lean_object* v_ys_4758_, lean_object* v_type_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4755_, v_xs_4756_, v_tail_4757_, v_ys_4758_, v_type_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
lean_dec_ref(v_ys_4758_);
lean_dec(v___x_4755_);
return v_res_4765_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4766_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4767_ = lean_unsigned_to_nat(8u);
v___x_4768_ = lean_unsigned_to_nat(349u);
v___x_4769_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4770_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4771_ = l_mkPanicMessageWithDecl(v___x_4770_, v___x_4769_, v___x_4768_, v___x_4767_, v___x_4766_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4772_, lean_object* v_x_4773_, lean_object* v_x_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_){
_start:
{
if (lean_obj_tag(v_x_4773_) == 0)
{
lean_object* v___x_4780_; 
lean_dec(v_a_4778_);
lean_dec_ref(v_a_4777_);
lean_dec(v_a_4776_);
lean_dec_ref(v_a_4775_);
lean_dec_ref(v_xs_4772_);
v___x_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4780_, 0, v_x_4774_);
return v___x_4780_;
}
else
{
lean_object* v_head_4781_; 
v_head_4781_ = lean_ctor_get(v_x_4773_, 0);
if (lean_obj_tag(v_head_4781_) == 0)
{
lean_object* v_tail_4782_; lean_object* v___x_4783_; lean_object* v___f_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; lean_object* v___x_4787_; 
v_tail_4782_ = lean_ctor_get(v_x_4773_, 1);
lean_inc(v_tail_4782_);
lean_dec_ref(v_x_4773_);
v___x_4783_ = lean_unsigned_to_nat(1u);
v___f_4784_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4784_, 0, v___x_4783_);
lean_closure_set(v___f_4784_, 1, v_xs_4772_);
lean_closure_set(v___f_4784_, 2, v_tail_4782_);
v___x_4785_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4786_ = 0;
v___x_4787_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4774_, v___x_4785_, v___f_4784_, v___x_4786_, v___x_4786_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
return v___x_4787_;
}
else
{
lean_object* v_tail_4788_; lean_object* v_val_4789_; lean_object* v___x_4790_; uint8_t v___x_4791_; 
lean_inc_ref(v_head_4781_);
v_tail_4788_ = lean_ctor_get(v_x_4773_, 1);
lean_inc(v_tail_4788_);
lean_dec_ref(v_x_4773_);
v_val_4789_ = lean_ctor_get(v_head_4781_, 0);
lean_inc(v_val_4789_);
lean_dec_ref(v_head_4781_);
v___x_4790_ = lean_array_get_size(v_xs_4772_);
v___x_4791_ = lean_nat_dec_lt(v_val_4789_, v___x_4790_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
lean_dec(v_val_4789_);
lean_dec(v_tail_4788_);
lean_dec_ref(v_x_4774_);
lean_dec_ref(v_xs_4772_);
v___x_4792_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4793_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4792_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
return v___x_4793_;
}
else
{
lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4794_ = l_Lean_instInhabitedExpr;
v___x_4795_ = lean_array_get_borrowed(v___x_4794_, v_xs_4772_, v_val_4789_);
lean_dec(v_val_4789_);
v___x_4796_ = lean_unsigned_to_nat(1u);
v___x_4797_ = lean_mk_empty_array_with_capacity(v___x_4796_);
lean_inc(v___x_4795_);
v___x_4798_ = lean_array_push(v___x_4797_, v___x_4795_);
lean_inc(v_a_4778_);
lean_inc_ref(v_a_4777_);
lean_inc(v_a_4776_);
lean_inc_ref(v_a_4775_);
v___x_4799_ = l_Lean_Meta_instantiateForall(v_x_4774_, v___x_4798_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
lean_dec_ref(v___x_4798_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
lean_inc(v_a_4800_);
lean_dec_ref(v___x_4799_);
v_x_4773_ = v_tail_4788_;
v_x_4774_ = v_a_4800_;
goto _start;
}
else
{
lean_dec(v_tail_4788_);
lean_dec(v_a_4778_);
lean_dec_ref(v_a_4777_);
lean_dec(v_a_4776_);
lean_dec_ref(v_a_4775_);
lean_dec_ref(v_xs_4772_);
return v___x_4799_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4802_, lean_object* v_xs_4803_, lean_object* v_tail_4804_, lean_object* v_ys_4805_, lean_object* v_type_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v___x_4812_; uint8_t v___x_4813_; 
v___x_4812_ = lean_array_get_size(v_ys_4805_);
v___x_4813_ = lean_nat_dec_eq(v___x_4812_, v___x_4802_);
if (v___x_4813_ == 0)
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
lean_dec_ref(v_type_4806_);
lean_dec(v_tail_4804_);
lean_dec_ref(v_xs_4803_);
v___x_4814_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4815_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4814_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
return v___x_4815_;
}
else
{
lean_object* v___x_4816_; 
lean_inc(v___y_4810_);
lean_inc_ref(v___y_4809_);
lean_inc(v___y_4808_);
lean_inc_ref(v___y_4807_);
v___x_4816_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4803_, v_tail_4804_, v_type_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_object* v_a_4817_; uint8_t v___x_4818_; uint8_t v___x_4819_; lean_object* v___x_4820_; 
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
lean_inc(v_a_4817_);
lean_dec_ref(v___x_4816_);
v___x_4818_ = 0;
v___x_4819_ = 1;
v___x_4820_ = l_Lean_Meta_mkForallFVars(v_ys_4805_, v_a_4817_, v___x_4818_, v___x_4813_, v___x_4813_, v___x_4819_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec(v___y_4808_);
lean_dec_ref(v___y_4807_);
return v___x_4820_;
}
else
{
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec(v___y_4808_);
lean_dec_ref(v___y_4807_);
return v___x_4816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4821_, lean_object* v_x_4822_, lean_object* v_x_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4821_, v_x_4822_, v_x_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_);
return v_res_4829_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4832_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4833_ = lean_unsigned_to_nat(2u);
v___x_4834_ = lean_unsigned_to_nat(343u);
v___x_4835_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4836_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4837_ = l_mkPanicMessageWithDecl(v___x_4836_, v___x_4835_, v___x_4834_, v___x_4833_, v___x_4832_);
return v___x_4837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4838_, lean_object* v_type_u2080_4839_, lean_object* v_xs_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; uint8_t v___x_4848_; 
v___x_4846_ = lean_array_get_size(v_xs_4840_);
v___x_4847_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4838_);
v___x_4848_ = lean_nat_dec_eq(v___x_4846_, v___x_4847_);
lean_dec(v___x_4847_);
if (v___x_4848_ == 0)
{
lean_object* v___x_4849_; lean_object* v___x_4850_; 
lean_dec_ref(v_xs_4840_);
lean_dec_ref(v_type_u2080_4839_);
lean_dec_ref(v_perm_4838_);
v___x_4849_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4850_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4849_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_);
return v___x_4850_;
}
else
{
lean_object* v_mask_4851_; lean_object* v___x_4852_; 
v_mask_4851_ = lean_array_to_list(v_perm_4838_);
v___x_4852_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4840_, v_mask_4851_, v_type_u2080_4839_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_);
return v___x_4852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4853_, lean_object* v_type_u2080_4854_, lean_object* v_xs_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4853_, v_type_u2080_4854_, v_xs_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(lean_object* v_e_4862_, lean_object* v_maxFVars_4863_, lean_object* v_k_4864_, uint8_t v_cleanupAnnotations_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_){
_start:
{
lean_object* v___f_4871_; uint8_t v___x_4872_; uint8_t v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; 
v___f_4871_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4871_, 0, v_k_4864_);
v___x_4872_ = 1;
v___x_4873_ = 0;
v___x_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4874_, 0, v_maxFVars_4863_);
v___x_4875_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4862_, v___x_4872_, v___x_4873_, v___x_4872_, v___x_4873_, v___x_4874_, v___f_4871_, v_cleanupAnnotations_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_);
lean_dec_ref(v___x_4874_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4878_ = v___x_4875_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4875_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4881_; 
if (v_isShared_4879_ == 0)
{
v___x_4881_ = v___x_4878_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_a_4876_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
else
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
v_a_4884_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4875_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4875_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4889_; 
if (v_isShared_4887_ == 0)
{
v___x_4889_ = v___x_4886_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4884_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg___boxed(lean_object* v_e_4892_, lean_object* v_maxFVars_4893_, lean_object* v_k_4894_, lean_object* v_cleanupAnnotations_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4901_; lean_object* v_res_4902_; 
v_cleanupAnnotations_boxed_4901_ = lean_unbox(v_cleanupAnnotations_4895_);
v_res_4902_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(v_e_4892_, v_maxFVars_4893_, v_k_4894_, v_cleanupAnnotations_boxed_4901_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_);
return v_res_4902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_00_u03b1_4903_, lean_object* v_e_4904_, lean_object* v_maxFVars_4905_, lean_object* v_k_4906_, uint8_t v_cleanupAnnotations_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_){
_start:
{
lean_object* v___x_4913_; 
v___x_4913_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(v_e_4904_, v_maxFVars_4905_, v_k_4906_, v_cleanupAnnotations_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_00_u03b1_4914_, lean_object* v_e_4915_, lean_object* v_maxFVars_4916_, lean_object* v_k_4917_, lean_object* v_cleanupAnnotations_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4924_; lean_object* v_res_4925_; 
v_cleanupAnnotations_boxed_4924_ = lean_unbox(v_cleanupAnnotations_4918_);
v_res_4925_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_00_u03b1_4914_, v_e_4915_, v_maxFVars_4916_, v_k_4917_, v_cleanupAnnotations_boxed_4924_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_);
return v_res_4925_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___y_4926_){
_start:
{
if (lean_obj_tag(v___y_4926_) == 0)
{
uint8_t v___x_4927_; 
v___x_4927_ = 1;
return v___x_4927_;
}
else
{
uint8_t v___x_4928_; 
v___x_4928_ = 0;
return v___x_4928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___y_4929_){
_start:
{
uint8_t v_res_4930_; lean_object* v_r_4931_; 
v_res_4930_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___y_4929_);
lean_dec(v___y_4929_);
v_r_4931_ = lean_box(v_res_4930_);
return v_r_4931_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2(void){
_start:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4934_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__1));
v___x_4935_ = lean_unsigned_to_nat(12u);
v___x_4936_ = lean_unsigned_to_nat(376u);
v___x_4937_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__0));
v___x_4938_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4939_ = l_mkPanicMessageWithDecl(v___x_4938_, v___x_4937_, v___x_4936_, v___x_4935_, v___x_4934_);
return v___x_4939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___boxed(lean_object* v___x_4941_, lean_object* v_xs_4942_, lean_object* v_tail_4943_, lean_object* v___x_4944_, lean_object* v___x_4945_, lean_object* v_ys_4946_, lean_object* v_value_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_){
_start:
{
uint8_t v___x_1377__boxed_4953_; uint8_t v___x_1378__boxed_4954_; lean_object* v_res_4955_; 
v___x_1377__boxed_4953_ = lean_unbox(v___x_4944_);
v___x_1378__boxed_4954_ = lean_unbox(v___x_4945_);
v_res_4955_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1(v___x_4941_, v_xs_4942_, v_tail_4943_, v___x_1377__boxed_4953_, v___x_1378__boxed_4954_, v_ys_4946_, v_value_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
lean_dec_ref(v_ys_4946_);
lean_dec(v___x_4941_);
return v_res_4955_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1(void){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4956_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4957_ = lean_unsigned_to_nat(8u);
v___x_4958_ = lean_unsigned_to_nat(368u);
v___x_4959_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__0));
v___x_4960_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4961_ = l_mkPanicMessageWithDecl(v___x_4960_, v___x_4959_, v___x_4958_, v___x_4957_, v___x_4956_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4962_, lean_object* v_x_4963_, lean_object* v_x_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_){
_start:
{
if (lean_obj_tag(v_x_4963_) == 0)
{
lean_object* v___x_4970_; 
lean_dec(v_a_4968_);
lean_dec_ref(v_a_4967_);
lean_dec(v_a_4966_);
lean_dec_ref(v_a_4965_);
lean_dec_ref(v_xs_4962_);
v___x_4970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4970_, 0, v_x_4964_);
return v___x_4970_;
}
else
{
lean_object* v_head_4971_; 
v_head_4971_ = lean_ctor_get(v_x_4963_, 0);
if (lean_obj_tag(v_head_4971_) == 0)
{
lean_object* v_tail_4972_; lean_object* v___f_4973_; uint8_t v___x_4974_; 
v_tail_4972_ = lean_ctor_get(v_x_4963_, 1);
lean_inc(v_tail_4972_);
lean_dec_ref(v_x_4963_);
v___f_4973_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0));
lean_inc(v_tail_4972_);
v___x_4974_ = l_List_all___redArg(v_tail_4972_, v___f_4973_);
if (v___x_4974_ == 0)
{
uint8_t v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___f_4979_; lean_object* v___x_4980_; 
v___x_4975_ = 1;
v___x_4976_ = lean_unsigned_to_nat(1u);
v___x_4977_ = lean_box(v___x_4974_);
v___x_4978_ = lean_box(v___x_4975_);
v___f_4979_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4979_, 0, v___x_4976_);
lean_closure_set(v___f_4979_, 1, v_xs_4962_);
lean_closure_set(v___f_4979_, 2, v_tail_4972_);
lean_closure_set(v___f_4979_, 3, v___x_4977_);
lean_closure_set(v___f_4979_, 4, v___x_4978_);
v___x_4980_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(v_x_4964_, v___x_4976_, v___f_4979_, v___x_4974_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_);
return v___x_4980_;
}
else
{
lean_object* v___x_4981_; 
lean_dec(v_tail_4972_);
lean_dec(v_a_4968_);
lean_dec_ref(v_a_4967_);
lean_dec(v_a_4966_);
lean_dec_ref(v_a_4965_);
lean_dec_ref(v_xs_4962_);
v___x_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4981_, 0, v_x_4964_);
return v___x_4981_;
}
}
else
{
lean_object* v_tail_4982_; lean_object* v_val_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; 
lean_inc_ref(v_head_4971_);
v_tail_4982_ = lean_ctor_get(v_x_4963_, 1);
lean_inc(v_tail_4982_);
lean_dec_ref(v_x_4963_);
v_val_4983_ = lean_ctor_get(v_head_4971_, 0);
lean_inc(v_val_4983_);
lean_dec_ref(v_head_4971_);
v___x_4984_ = lean_array_get_size(v_xs_4962_);
v___x_4985_ = lean_nat_dec_lt(v_val_4983_, v___x_4984_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; lean_object* v___x_4987_; 
lean_dec(v_val_4983_);
lean_dec(v_tail_4982_);
lean_dec_ref(v_x_4964_);
lean_dec_ref(v_xs_4962_);
v___x_4986_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1);
v___x_4987_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4986_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_);
return v___x_4987_;
}
else
{
lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4988_ = l_Lean_instInhabitedExpr;
v___x_4989_ = lean_array_get_borrowed(v___x_4988_, v_xs_4962_, v_val_4983_);
lean_dec(v_val_4983_);
v___x_4990_ = lean_unsigned_to_nat(1u);
v___x_4991_ = lean_mk_empty_array_with_capacity(v___x_4990_);
lean_inc(v___x_4989_);
v___x_4992_ = lean_array_push(v___x_4991_, v___x_4989_);
lean_inc(v_a_4968_);
lean_inc_ref(v_a_4967_);
lean_inc(v_a_4966_);
lean_inc_ref(v_a_4965_);
v___x_4993_ = l_Lean_Meta_instantiateLambda(v_x_4964_, v___x_4992_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_);
lean_dec_ref(v___x_4992_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v_a_4994_; 
v_a_4994_ = lean_ctor_get(v___x_4993_, 0);
lean_inc(v_a_4994_);
lean_dec_ref(v___x_4993_);
v_x_4963_ = v_tail_4982_;
v_x_4964_ = v_a_4994_;
goto _start;
}
else
{
lean_dec(v_tail_4982_);
lean_dec(v_a_4968_);
lean_dec_ref(v_a_4967_);
lean_dec(v_a_4966_);
lean_dec_ref(v_a_4965_);
lean_dec_ref(v_xs_4962_);
return v___x_4993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1(lean_object* v___x_4996_, lean_object* v_xs_4997_, lean_object* v_tail_4998_, uint8_t v___x_4999_, uint8_t v___x_5000_, lean_object* v_ys_5001_, lean_object* v_value_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v___x_5008_; uint8_t v___x_5009_; 
v___x_5008_ = lean_array_get_size(v_ys_5001_);
v___x_5009_ = lean_nat_dec_eq(v___x_5008_, v___x_4996_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; lean_object* v___x_5011_; 
lean_dec_ref(v_value_5002_);
lean_dec(v_tail_4998_);
lean_dec_ref(v_xs_4997_);
v___x_5010_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2);
v___x_5011_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5010_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
return v___x_5011_;
}
else
{
lean_object* v___x_5012_; 
lean_inc(v___y_5006_);
lean_inc_ref(v___y_5005_);
lean_inc(v___y_5004_);
lean_inc_ref(v___y_5003_);
v___x_5012_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4997_, v_tail_4998_, v_value_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; uint8_t v___x_5014_; lean_object* v___x_5015_; 
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
lean_inc(v_a_5013_);
lean_dec_ref(v___x_5012_);
v___x_5014_ = 1;
v___x_5015_ = l_Lean_Meta_mkLambdaFVars(v_ys_5001_, v_a_5013_, v___x_4999_, v___x_5000_, v___x_4999_, v___x_5000_, v___x_5014_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
lean_dec(v___y_5004_);
lean_dec_ref(v___y_5003_);
return v___x_5015_;
}
else
{
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
lean_dec(v___y_5004_);
lean_dec_ref(v___y_5003_);
return v___x_5012_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_5016_, lean_object* v_x_5017_, lean_object* v_x_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_){
_start:
{
lean_object* v_res_5024_; 
v_res_5024_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5016_, v_x_5017_, v_x_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_);
return v_res_5024_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5026_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_5027_ = lean_unsigned_to_nat(2u);
v___x_5028_ = lean_unsigned_to_nat(362u);
v___x_5029_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_5030_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5031_ = l_mkPanicMessageWithDecl(v___x_5030_, v___x_5029_, v___x_5028_, v___x_5027_, v___x_5026_);
return v___x_5031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_5032_, lean_object* v_value_u2080_5033_, lean_object* v_xs_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; uint8_t v___x_5042_; 
v___x_5040_ = lean_array_get_size(v_xs_5034_);
v___x_5041_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5032_);
v___x_5042_ = lean_nat_dec_eq(v___x_5040_, v___x_5041_);
lean_dec(v___x_5041_);
if (v___x_5042_ == 0)
{
lean_object* v___x_5043_; lean_object* v___x_5044_; 
lean_dec_ref(v_xs_5034_);
lean_dec_ref(v_value_u2080_5033_);
lean_dec_ref(v_perm_5032_);
v___x_5043_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_5044_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5043_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
return v___x_5044_;
}
else
{
lean_object* v_mask_5045_; lean_object* v___x_5046_; 
v_mask_5045_ = lean_array_to_list(v_perm_5032_);
v___x_5046_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5034_, v_mask_5045_, v_value_u2080_5033_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
return v___x_5046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_5047_, lean_object* v_value_u2080_5048_, lean_object* v_xs_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_5047_, v_value_u2080_5048_, v_xs_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_);
return v_res_5055_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_5063_; 
v___x_5063_ = l_Array_instInhabited(lean_box(0));
return v___x_5063_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5064_){
_start:
{
lean_object* v___f_5065_; lean_object* v___f_5066_; lean_object* v___f_5067_; lean_object* v___f_5068_; lean_object* v___f_5069_; lean_object* v___f_5070_; lean_object* v___f_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___f_5065_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5066_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5067_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5068_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5069_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5070_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5071_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5072_, 0, v___f_5065_);
lean_ctor_set(v___x_5072_, 1, v___f_5066_);
v___x_5073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5073_, 0, v___x_5072_);
lean_ctor_set(v___x_5073_, 1, v___f_5067_);
lean_ctor_set(v___x_5073_, 2, v___f_5068_);
lean_ctor_set(v___x_5073_, 3, v___f_5069_);
lean_ctor_set(v___x_5073_, 4, v___f_5070_);
v___x_5074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5074_, 0, v___x_5073_);
lean_ctor_set(v___x_5074_, 1, v___f_5071_);
v___x_5075_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5076_ = l_instInhabitedOfMonad___redArg(v___x_5074_, v___x_5075_);
v___x_5077_ = lean_panic_fn(v___x_5076_, v_msg_5064_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5078_, lean_object* v_msg_5079_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5079_);
return v___x_5080_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; 
v___x_5083_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5084_ = lean_unsigned_to_nat(8u);
v___x_5085_ = lean_unsigned_to_nat(394u);
v___x_5086_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5087_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5088_ = l_mkPanicMessageWithDecl(v___x_5087_, v___x_5086_, v___x_5085_, v___x_5084_, v___x_5083_);
return v___x_5088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5089_, lean_object* v_x_5090_){
_start:
{
if (lean_obj_tag(v_x_5089_) == 0)
{
return v_x_5090_;
}
else
{
lean_object* v_head_5091_; lean_object* v_fst_5092_; 
v_head_5091_ = lean_ctor_get(v_x_5089_, 0);
v_fst_5092_ = lean_ctor_get(v_head_5091_, 0);
if (lean_obj_tag(v_fst_5092_) == 0)
{
lean_object* v_tail_5093_; 
v_tail_5093_ = lean_ctor_get(v_x_5089_, 1);
lean_inc(v_tail_5093_);
lean_dec_ref(v_x_5089_);
v_x_5089_ = v_tail_5093_;
goto _start;
}
else
{
lean_object* v_tail_5095_; lean_object* v_snd_5096_; lean_object* v_val_5097_; lean_object* v___x_5098_; uint8_t v___x_5099_; 
lean_inc_ref(v_fst_5092_);
lean_inc(v_head_5091_);
v_tail_5095_ = lean_ctor_get(v_x_5089_, 1);
lean_inc(v_tail_5095_);
lean_dec_ref(v_x_5089_);
v_snd_5096_ = lean_ctor_get(v_head_5091_, 1);
lean_inc(v_snd_5096_);
lean_dec(v_head_5091_);
v_val_5097_ = lean_ctor_get(v_fst_5092_, 0);
lean_inc(v_val_5097_);
lean_dec_ref(v_fst_5092_);
v___x_5098_ = lean_array_get_size(v_x_5090_);
v___x_5099_ = lean_nat_dec_lt(v_val_5097_, v___x_5098_);
if (v___x_5099_ == 0)
{
lean_object* v___x_5100_; lean_object* v___x_5101_; 
lean_dec(v_val_5097_);
lean_dec(v_snd_5096_);
lean_dec(v_tail_5095_);
lean_dec_ref(v_x_5090_);
v___x_5100_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5101_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5100_);
return v___x_5101_;
}
else
{
lean_object* v___x_5102_; 
v___x_5102_ = lean_array_set(v_x_5090_, v_val_5097_, v_snd_5096_);
lean_dec(v_val_5097_);
v_x_5089_ = v_tail_5095_;
v_x_5090_ = v___x_5102_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5104_, lean_object* v_x_5105_, lean_object* v_x_5106_){
_start:
{
lean_object* v___x_5107_; 
v___x_5107_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5105_, v_x_5106_);
return v___x_5107_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; 
v___x_5110_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5111_ = lean_unsigned_to_nat(2u);
v___x_5112_ = lean_unsigned_to_nat(384u);
v___x_5113_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5114_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5115_ = l_mkPanicMessageWithDecl(v___x_5114_, v___x_5113_, v___x_5112_, v___x_5111_, v___x_5110_);
return v___x_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5118_, lean_object* v_xs_5119_){
_start:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; uint8_t v___x_5122_; 
v___x_5120_ = lean_array_get_size(v_xs_5119_);
v___x_5121_ = lean_array_get_size(v_perm_5118_);
v___x_5122_ = lean_nat_dec_eq(v___x_5120_, v___x_5121_);
if (v___x_5122_ == 0)
{
lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___x_5123_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5124_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5123_);
return v___x_5124_;
}
else
{
lean_object* v___x_5125_; uint8_t v___x_5126_; 
v___x_5125_ = lean_unsigned_to_nat(0u);
v___x_5126_ = lean_nat_dec_eq(v___x_5120_, v___x_5125_);
if (v___x_5126_ == 0)
{
lean_object* v_dummy_5127_; lean_object* v___x_5128_; lean_object* v_ys_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; 
v_dummy_5127_ = lean_array_fget_borrowed(v_xs_5119_, v___x_5125_);
v___x_5128_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5118_);
lean_inc(v_dummy_5127_);
v_ys_5129_ = lean_mk_array(v___x_5128_, v_dummy_5127_);
v___x_5130_ = l_Array_zip___redArg(v_perm_5118_, v_xs_5119_);
v___x_5131_ = lean_array_to_list(v___x_5130_);
v___x_5132_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5131_, v_ys_5129_);
return v___x_5132_;
}
else
{
lean_object* v___x_5133_; 
v___x_5133_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5134_, lean_object* v_xs_5135_){
_start:
{
lean_object* v_res_5136_; 
v_res_5136_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5134_, v_xs_5135_);
lean_dec_ref(v_xs_5135_);
lean_dec_ref(v_perm_5134_);
return v_res_5136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5137_, lean_object* v_perm_5138_, lean_object* v_xs_5139_){
_start:
{
lean_object* v___x_5140_; 
v___x_5140_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5138_, v_xs_5139_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5141_, lean_object* v_perm_5142_, lean_object* v_xs_5143_){
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5141_, v_perm_5142_, v_xs_5143_);
lean_dec_ref(v_xs_5143_);
lean_dec_ref(v_perm_5142_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5145_, lean_object* v_upperBound_5146_, lean_object* v_perm_5147_, lean_object* v_a_5148_, lean_object* v_b_5149_){
_start:
{
lean_object* v_a_5151_; uint8_t v___x_5158_; 
v___x_5158_ = lean_nat_dec_lt(v_a_5148_, v_upperBound_5146_);
if (v___x_5158_ == 0)
{
lean_dec(v_a_5148_);
return v_b_5149_;
}
else
{
lean_object* v___x_5159_; uint8_t v___x_5160_; 
v___x_5159_ = lean_array_get_size(v_perm_5147_);
v___x_5160_ = lean_nat_dec_lt(v_a_5148_, v___x_5159_);
if (v___x_5160_ == 0)
{
goto v___jp_5155_;
}
else
{
lean_object* v___x_5161_; 
v___x_5161_ = lean_array_fget_borrowed(v_perm_5147_, v_a_5148_);
if (lean_obj_tag(v___x_5161_) == 0)
{
goto v___jp_5155_;
}
else
{
v_a_5151_ = v_b_5149_;
goto v___jp_5150_;
}
}
}
v___jp_5150_:
{
lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___x_5152_ = lean_unsigned_to_nat(1u);
v___x_5153_ = lean_nat_add(v_a_5148_, v___x_5152_);
lean_dec(v_a_5148_);
v_a_5148_ = v___x_5153_;
v_b_5149_ = v_a_5151_;
goto _start;
}
v___jp_5155_:
{
lean_object* v___x_5156_; lean_object* v___x_5157_; 
v___x_5156_ = lean_array_fget_borrowed(v_xs_5145_, v_a_5148_);
lean_inc(v___x_5156_);
v___x_5157_ = lean_array_push(v_b_5149_, v___x_5156_);
v_a_5151_ = v___x_5157_;
goto v___jp_5150_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5162_, lean_object* v_upperBound_5163_, lean_object* v_perm_5164_, lean_object* v_a_5165_, lean_object* v_b_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5162_, v_upperBound_5163_, v_perm_5164_, v_a_5165_, v_b_5166_);
lean_dec_ref(v_perm_5164_);
lean_dec(v_upperBound_5163_);
lean_dec_ref(v_xs_5162_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5168_, lean_object* v_xs_5169_){
_start:
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v_ys_5172_; lean_object* v___x_5173_; 
v___x_5170_ = lean_array_get_size(v_xs_5169_);
v___x_5171_ = lean_unsigned_to_nat(0u);
v_ys_5172_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5173_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5169_, v___x_5170_, v_perm_5168_, v___x_5171_, v_ys_5172_);
return v___x_5173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5174_, lean_object* v_xs_5175_){
_start:
{
lean_object* v_res_5176_; 
v_res_5176_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5174_, v_xs_5175_);
lean_dec_ref(v_xs_5175_);
lean_dec_ref(v_perm_5174_);
return v_res_5176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5177_, lean_object* v_perm_5178_, lean_object* v_xs_5179_){
_start:
{
lean_object* v___x_5180_; 
v___x_5180_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5178_, v_xs_5179_);
return v___x_5180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5181_, lean_object* v_perm_5182_, lean_object* v_xs_5183_){
_start:
{
lean_object* v_res_5184_; 
v_res_5184_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5181_, v_perm_5182_, v_xs_5183_);
lean_dec_ref(v_xs_5183_);
lean_dec_ref(v_perm_5182_);
return v_res_5184_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5185_, lean_object* v_xs_5186_, lean_object* v_upperBound_5187_, lean_object* v_perm_5188_, lean_object* v_inst_5189_, lean_object* v_R_5190_, lean_object* v_a_5191_, lean_object* v_b_5192_, lean_object* v_c_5193_){
_start:
{
lean_object* v___x_5194_; 
v___x_5194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5186_, v_upperBound_5187_, v_perm_5188_, v_a_5191_, v_b_5192_);
return v___x_5194_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5195_, lean_object* v_xs_5196_, lean_object* v_upperBound_5197_, lean_object* v_perm_5198_, lean_object* v_inst_5199_, lean_object* v_R_5200_, lean_object* v_a_5201_, lean_object* v_b_5202_, lean_object* v_c_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5195_, v_xs_5196_, v_upperBound_5197_, v_perm_5198_, v_inst_5199_, v_R_5200_, v_a_5201_, v_b_5202_, v_c_5203_);
lean_dec_ref(v_perm_5198_);
lean_dec(v_upperBound_5197_);
lean_dec_ref(v_xs_5196_);
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(lean_object* v_msg_5205_){
_start:
{
lean_object* v___x_5206_; lean_object* v___x_5207_; 
v___x_5206_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5207_ = lean_panic_fn(v___x_5206_, v_msg_5205_);
return v___x_5207_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_00_u03b1_5208_, lean_object* v_msg_5209_){
_start:
{
lean_object* v___x_5210_; 
v___x_5210_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v_msg_5209_);
return v___x_5210_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_as_5211_, size_t v_i_5212_, size_t v_stop_5213_){
_start:
{
uint8_t v___x_5214_; 
v___x_5214_ = lean_usize_dec_eq(v_i_5212_, v_stop_5213_);
if (v___x_5214_ == 0)
{
uint8_t v___x_5215_; lean_object* v___x_5216_; 
v___x_5215_ = 1;
v___x_5216_ = lean_array_uget_borrowed(v_as_5211_, v_i_5212_);
if (lean_obj_tag(v___x_5216_) == 0)
{
if (v___x_5214_ == 0)
{
size_t v___x_5217_; size_t v___x_5218_; 
v___x_5217_ = ((size_t)1ULL);
v___x_5218_ = lean_usize_add(v_i_5212_, v___x_5217_);
v_i_5212_ = v___x_5218_;
goto _start;
}
else
{
return v___x_5215_;
}
}
else
{
return v___x_5215_;
}
}
else
{
uint8_t v___x_5220_; 
v___x_5220_ = 0;
return v___x_5220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___boxed(lean_object* v_as_5221_, lean_object* v_i_5222_, lean_object* v_stop_5223_){
_start:
{
size_t v_i_boxed_5224_; size_t v_stop_boxed_5225_; uint8_t v_res_5226_; lean_object* v_r_5227_; 
v_i_boxed_5224_ = lean_unbox_usize(v_i_5222_);
lean_dec(v_i_5222_);
v_stop_boxed_5225_ = lean_unbox_usize(v_stop_5223_);
lean_dec(v_stop_5223_);
v_res_5226_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v_as_5221_, v_i_boxed_5224_, v_stop_boxed_5225_);
lean_dec_ref(v_as_5221_);
v_r_5227_ = lean_box(v_res_5226_);
return v_r_5227_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; 
v___x_5230_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5231_ = lean_unsigned_to_nat(12u);
v___x_5232_ = lean_unsigned_to_nat(433u);
v___x_5233_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5234_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5235_ = l_mkPanicMessageWithDecl(v___x_5234_, v___x_5233_, v___x_5232_, v___x_5231_, v___x_5230_);
return v___x_5235_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; 
v___x_5237_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5238_ = lean_unsigned_to_nat(10u);
v___x_5239_ = lean_unsigned_to_nat(425u);
v___x_5240_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5241_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5242_ = l_mkPanicMessageWithDecl(v___x_5241_, v___x_5240_, v___x_5239_, v___x_5238_, v___x_5237_);
return v___x_5242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5243_, lean_object* v_fixedArgs_5244_, lean_object* v_varyingArgs_5245_, lean_object* v_i_5246_, lean_object* v_j_5247_, lean_object* v_xs_5248_){
_start:
{
lean_object* v_lower_5250_; lean_object* v_upper_5251_; lean_object* v___y_5256_; lean_object* v___y_5257_; lean_object* v___y_5258_; lean_object* v_lower_5266_; lean_object* v_upper_5267_; lean_object* v___x_5275_; uint8_t v___x_5276_; 
v___x_5275_ = lean_array_get_size(v_perm_5243_);
v___x_5276_ = lean_nat_dec_lt(v_i_5246_, v___x_5275_);
if (v___x_5276_ == 0)
{
lean_object* v___x_5277_; lean_object* v___x_5278_; uint8_t v___x_5279_; 
lean_dec(v_i_5246_);
lean_dec_ref(v_perm_5243_);
v___x_5277_ = lean_unsigned_to_nat(0u);
v___x_5278_ = lean_array_get_size(v_varyingArgs_5245_);
v___x_5279_ = lean_nat_dec_le(v_j_5247_, v___x_5277_);
if (v___x_5279_ == 0)
{
v_lower_5250_ = v_j_5247_;
v_upper_5251_ = v___x_5278_;
goto v___jp_5249_;
}
else
{
lean_dec(v_j_5247_);
v_lower_5250_ = v___x_5277_;
v_upper_5251_ = v___x_5278_;
goto v___jp_5249_;
}
}
else
{
lean_object* v___x_5280_; 
v___x_5280_ = lean_array_fget_borrowed(v_perm_5243_, v_i_5246_);
if (lean_obj_tag(v___x_5280_) == 1)
{
lean_object* v_val_5281_; lean_object* v___x_5282_; uint8_t v___x_5283_; 
v_val_5281_ = lean_ctor_get(v___x_5280_, 0);
v___x_5282_ = lean_array_get_size(v_fixedArgs_5244_);
v___x_5283_ = lean_nat_dec_lt(v_val_5281_, v___x_5282_);
if (v___x_5283_ == 0)
{
lean_object* v___x_5284_; lean_object* v___x_5285_; 
lean_dec_ref(v_xs_5248_);
lean_dec(v_j_5247_);
lean_dec(v_i_5246_);
lean_dec_ref(v_varyingArgs_5245_);
lean_dec_ref(v_perm_5243_);
v___x_5284_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5285_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5284_);
return v___x_5285_;
}
else
{
lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; 
v___x_5286_ = lean_unsigned_to_nat(1u);
v___x_5287_ = lean_nat_add(v_i_5246_, v___x_5286_);
lean_dec(v_i_5246_);
v___x_5288_ = lean_array_fget_borrowed(v_fixedArgs_5244_, v_val_5281_);
lean_inc(v___x_5288_);
v___x_5289_ = lean_array_push(v_xs_5248_, v___x_5288_);
v_i_5246_ = v___x_5287_;
v_xs_5248_ = v___x_5289_;
goto _start;
}
}
else
{
lean_object* v___x_5291_; uint8_t v___x_5292_; 
v___x_5291_ = lean_array_get_size(v_varyingArgs_5245_);
v___x_5292_ = lean_nat_dec_lt(v_j_5247_, v___x_5291_);
if (v___x_5292_ == 0)
{
lean_object* v___x_5293_; uint8_t v___x_5294_; 
lean_dec(v_j_5247_);
lean_dec_ref(v_varyingArgs_5245_);
v___x_5293_ = lean_unsigned_to_nat(0u);
v___x_5294_ = lean_nat_dec_le(v_i_5246_, v___x_5293_);
if (v___x_5294_ == 0)
{
v_lower_5266_ = v_i_5246_;
v_upper_5267_ = v___x_5275_;
goto v___jp_5265_;
}
else
{
lean_dec(v_i_5246_);
v_lower_5266_ = v___x_5293_;
v_upper_5267_ = v___x_5275_;
goto v___jp_5265_;
}
}
else
{
lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; 
v___x_5295_ = lean_unsigned_to_nat(1u);
v___x_5296_ = lean_nat_add(v_i_5246_, v___x_5295_);
lean_dec(v_i_5246_);
v___x_5297_ = lean_nat_add(v_j_5247_, v___x_5295_);
v___x_5298_ = lean_array_fget_borrowed(v_varyingArgs_5245_, v_j_5247_);
lean_dec(v_j_5247_);
lean_inc(v___x_5298_);
v___x_5299_ = lean_array_push(v_xs_5248_, v___x_5298_);
v_i_5246_ = v___x_5296_;
v_j_5247_ = v___x_5297_;
v_xs_5248_ = v___x_5299_;
goto _start;
}
}
}
v___jp_5249_:
{
lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; 
v___x_5252_ = l_Array_toSubarray___redArg(v_varyingArgs_5245_, v_lower_5250_, v_upper_5251_);
v___x_5253_ = l_Subarray_copy___redArg(v___x_5252_);
v___x_5254_ = l_Array_append___redArg(v_xs_5248_, v___x_5253_);
lean_dec_ref(v___x_5253_);
return v___x_5254_;
}
v___jp_5255_:
{
uint8_t v___x_5259_; 
v___x_5259_ = lean_nat_dec_lt(v___y_5256_, v___y_5258_);
if (v___x_5259_ == 0)
{
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
lean_dec(v___y_5256_);
return v_xs_5248_;
}
else
{
size_t v___x_5260_; size_t v___x_5261_; uint8_t v___x_5262_; 
v___x_5260_ = lean_usize_of_nat(v___y_5256_);
lean_dec(v___y_5256_);
v___x_5261_ = lean_usize_of_nat(v___y_5258_);
lean_dec(v___y_5258_);
v___x_5262_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v___y_5257_, v___x_5260_, v___x_5261_);
lean_dec_ref(v___y_5257_);
if (v___x_5262_ == 0)
{
return v_xs_5248_;
}
else
{
lean_object* v___x_5263_; lean_object* v___x_5264_; 
lean_dec_ref(v_xs_5248_);
v___x_5263_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5264_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5263_);
return v___x_5264_;
}
}
}
v___jp_5265_:
{
lean_object* v___x_5268_; lean_object* v_array_5269_; lean_object* v_start_5270_; lean_object* v_stop_5271_; uint8_t v___x_5272_; 
v___x_5268_ = l_Array_toSubarray___redArg(v_perm_5243_, v_lower_5266_, v_upper_5267_);
v_array_5269_ = lean_ctor_get(v___x_5268_, 0);
lean_inc_ref(v_array_5269_);
v_start_5270_ = lean_ctor_get(v___x_5268_, 1);
lean_inc(v_start_5270_);
v_stop_5271_ = lean_ctor_get(v___x_5268_, 2);
lean_inc(v_stop_5271_);
lean_dec_ref(v___x_5268_);
v___x_5272_ = lean_nat_dec_lt(v_start_5270_, v_stop_5271_);
if (v___x_5272_ == 0)
{
lean_dec(v_stop_5271_);
lean_dec(v_start_5270_);
lean_dec_ref(v_array_5269_);
return v_xs_5248_;
}
else
{
lean_object* v___x_5273_; uint8_t v___x_5274_; 
v___x_5273_ = lean_array_get_size(v_array_5269_);
v___x_5274_ = lean_nat_dec_le(v_stop_5271_, v___x_5273_);
if (v___x_5274_ == 0)
{
lean_dec(v_stop_5271_);
v___y_5256_ = v_start_5270_;
v___y_5257_ = v_array_5269_;
v___y_5258_ = v___x_5273_;
goto v___jp_5255_;
}
else
{
v___y_5256_ = v_start_5270_;
v___y_5257_ = v_array_5269_;
v___y_5258_ = v_stop_5271_;
goto v___jp_5255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5301_, lean_object* v_fixedArgs_5302_, lean_object* v_varyingArgs_5303_, lean_object* v_i_5304_, lean_object* v_j_5305_, lean_object* v_xs_5306_){
_start:
{
lean_object* v_res_5307_; 
v_res_5307_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5301_, v_fixedArgs_5302_, v_varyingArgs_5303_, v_i_5304_, v_j_5305_, v_xs_5306_);
lean_dec_ref(v_fixedArgs_5302_);
return v_res_5307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5308_, lean_object* v_perm_5309_, lean_object* v_fixedArgs_5310_, lean_object* v_varyingArgs_5311_, lean_object* v_i_5312_, lean_object* v_j_5313_, lean_object* v_xs_5314_){
_start:
{
lean_object* v___x_5315_; 
v___x_5315_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5309_, v_fixedArgs_5310_, v_varyingArgs_5311_, v_i_5312_, v_j_5313_, v_xs_5314_);
return v___x_5315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5316_, lean_object* v_perm_5317_, lean_object* v_fixedArgs_5318_, lean_object* v_varyingArgs_5319_, lean_object* v_i_5320_, lean_object* v_j_5321_, lean_object* v_xs_5322_){
_start:
{
lean_object* v_res_5323_; 
v_res_5323_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5316_, v_perm_5317_, v_fixedArgs_5318_, v_varyingArgs_5319_, v_i_5320_, v_j_5321_, v_xs_5322_);
lean_dec_ref(v_fixedArgs_5318_);
return v_res_5323_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; 
v___x_5326_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5327_ = lean_unsigned_to_nat(2u);
v___x_5328_ = lean_unsigned_to_nat(416u);
v___x_5329_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5330_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5331_ = l_mkPanicMessageWithDecl(v___x_5330_, v___x_5329_, v___x_5328_, v___x_5327_, v___x_5326_);
return v___x_5331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5332_, lean_object* v_fixedArgs_5333_, lean_object* v_varyingArgs_5334_){
_start:
{
lean_object* v___x_5335_; lean_object* v___x_5336_; uint8_t v___x_5337_; 
v___x_5335_ = lean_array_get_size(v_fixedArgs_5333_);
v___x_5336_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5332_);
v___x_5337_ = lean_nat_dec_eq(v___x_5335_, v___x_5336_);
lean_dec(v___x_5336_);
if (v___x_5337_ == 0)
{
lean_object* v___x_5338_; lean_object* v___x_5339_; 
lean_dec_ref(v_varyingArgs_5334_);
lean_dec_ref(v_perm_5332_);
v___x_5338_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5339_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5338_);
return v___x_5339_;
}
else
{
lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; 
v___x_5340_ = lean_unsigned_to_nat(0u);
v___x_5341_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5342_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5332_, v_fixedArgs_5333_, v_varyingArgs_5334_, v___x_5340_, v___x_5340_, v___x_5341_);
return v___x_5342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5343_, lean_object* v_fixedArgs_5344_, lean_object* v_varyingArgs_5345_){
_start:
{
lean_object* v_res_5346_; 
v_res_5346_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5343_, v_fixedArgs_5344_, v_varyingArgs_5345_);
lean_dec_ref(v_fixedArgs_5344_);
return v_res_5346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5347_, lean_object* v_perm_5348_, lean_object* v_fixedArgs_5349_, lean_object* v_varyingArgs_5350_){
_start:
{
lean_object* v___x_5351_; 
v___x_5351_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5348_, v_fixedArgs_5349_, v_varyingArgs_5350_);
return v___x_5351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5352_, lean_object* v_perm_5353_, lean_object* v_fixedArgs_5354_, lean_object* v_varyingArgs_5355_){
_start:
{
lean_object* v_res_5356_; 
v_res_5356_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5352_, v_perm_5353_, v_fixedArgs_5354_, v_varyingArgs_5355_);
lean_dec_ref(v_fixedArgs_5354_);
return v_res_5356_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5357_, lean_object* v_x_5358_){
_start:
{
if (lean_obj_tag(v_x_5357_) == 0)
{
if (lean_obj_tag(v_x_5358_) == 0)
{
uint8_t v___x_5359_; 
v___x_5359_ = 1;
return v___x_5359_;
}
else
{
uint8_t v___x_5360_; 
v___x_5360_ = 0;
return v___x_5360_;
}
}
else
{
if (lean_obj_tag(v_x_5358_) == 0)
{
uint8_t v___x_5361_; 
v___x_5361_ = 0;
return v___x_5361_;
}
else
{
lean_object* v_val_5362_; lean_object* v_val_5363_; uint8_t v___x_5364_; 
v_val_5362_ = lean_ctor_get(v_x_5357_, 0);
v_val_5363_ = lean_ctor_get(v_x_5358_, 0);
v___x_5364_ = lean_nat_dec_eq(v_val_5362_, v_val_5363_);
return v___x_5364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5365_, lean_object* v_x_5366_){
_start:
{
uint8_t v_res_5367_; lean_object* v_r_5368_; 
v_res_5367_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5365_, v_x_5366_);
lean_dec(v_x_5366_);
lean_dec(v_x_5365_);
v_r_5368_ = lean_box(v_res_5367_);
return v_r_5368_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5369_, lean_object* v_ys_5370_, lean_object* v_x_5371_){
_start:
{
lean_object* v_zero_5372_; uint8_t v_isZero_5373_; 
v_zero_5372_ = lean_unsigned_to_nat(0u);
v_isZero_5373_ = lean_nat_dec_eq(v_x_5371_, v_zero_5372_);
if (v_isZero_5373_ == 1)
{
lean_dec(v_x_5371_);
return v_isZero_5373_;
}
else
{
lean_object* v_one_5374_; lean_object* v_n_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; uint8_t v___x_5378_; 
v_one_5374_ = lean_unsigned_to_nat(1u);
v_n_5375_ = lean_nat_sub(v_x_5371_, v_one_5374_);
lean_dec(v_x_5371_);
v___x_5376_ = lean_array_fget_borrowed(v_xs_5369_, v_n_5375_);
v___x_5377_ = lean_array_fget_borrowed(v_ys_5370_, v_n_5375_);
v___x_5378_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5376_, v___x_5377_);
if (v___x_5378_ == 0)
{
lean_dec(v_n_5375_);
return v___x_5378_;
}
else
{
v_x_5371_ = v_n_5375_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5380_, lean_object* v_ys_5381_, lean_object* v_x_5382_){
_start:
{
uint8_t v_res_5383_; lean_object* v_r_5384_; 
v_res_5383_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5380_, v_ys_5381_, v_x_5382_);
lean_dec_ref(v_ys_5381_);
lean_dec_ref(v_xs_5380_);
v_r_5384_ = lean_box(v_res_5383_);
return v_r_5384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5385_, size_t v_i_5386_, lean_object* v_bs_5387_){
_start:
{
uint8_t v___x_5388_; 
v___x_5388_ = lean_usize_dec_lt(v_i_5386_, v_sz_5385_);
if (v___x_5388_ == 0)
{
return v_bs_5387_;
}
else
{
lean_object* v_v_5389_; lean_object* v___x_5390_; lean_object* v_bs_x27_5391_; lean_object* v___x_5392_; size_t v___x_5393_; size_t v___x_5394_; lean_object* v___x_5395_; 
v_v_5389_ = lean_array_uget(v_bs_5387_, v_i_5386_);
v___x_5390_ = lean_unsigned_to_nat(0u);
v_bs_x27_5391_ = lean_array_uset(v_bs_5387_, v_i_5386_, v___x_5390_);
v___x_5392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5392_, 0, v_v_5389_);
v___x_5393_ = ((size_t)1ULL);
v___x_5394_ = lean_usize_add(v_i_5386_, v___x_5393_);
v___x_5395_ = lean_array_uset(v_bs_x27_5391_, v_i_5386_, v___x_5392_);
v_i_5386_ = v___x_5394_;
v_bs_5387_ = v___x_5395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5397_, lean_object* v_i_5398_, lean_object* v_bs_5399_){
_start:
{
size_t v_sz_boxed_5400_; size_t v_i_boxed_5401_; lean_object* v_res_5402_; 
v_sz_boxed_5400_ = lean_unbox_usize(v_sz_5397_);
lean_dec(v_sz_5397_);
v_i_boxed_5401_ = lean_unbox_usize(v_i_5398_);
lean_dec(v_i_5398_);
v_res_5402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5400_, v_i_boxed_5401_, v_bs_5399_);
return v_res_5402_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5403_, lean_object* v_as_5404_, size_t v_i_5405_, size_t v_stop_5406_){
_start:
{
uint8_t v___x_5407_; 
v___x_5407_ = lean_usize_dec_eq(v_i_5405_, v_stop_5406_);
if (v___x_5407_ == 0)
{
lean_object* v_numFixed_5408_; uint8_t v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; size_t v_sz_5412_; size_t v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; uint8_t v___x_5421_; 
v_numFixed_5408_ = lean_ctor_get(v_fixedParamPerms_5403_, 0);
v___x_5409_ = 1;
v___x_5410_ = lean_array_uget_borrowed(v_as_5404_, v_i_5405_);
lean_inc(v_numFixed_5408_);
v___x_5411_ = l_Array_range(v_numFixed_5408_);
v_sz_5412_ = lean_array_size(v___x_5411_);
v___x_5413_ = ((size_t)0ULL);
v___x_5414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5412_, v___x_5413_, v___x_5411_);
v___x_5415_ = lean_array_get_size(v___x_5410_);
v___x_5416_ = lean_nat_sub(v___x_5415_, v_numFixed_5408_);
v___x_5417_ = lean_box(0);
v___x_5418_ = lean_mk_array(v___x_5416_, v___x_5417_);
v___x_5419_ = l_Array_append___redArg(v___x_5414_, v___x_5418_);
lean_dec_ref(v___x_5418_);
v___x_5420_ = lean_array_get_size(v___x_5419_);
v___x_5421_ = lean_nat_dec_eq(v___x_5415_, v___x_5420_);
if (v___x_5421_ == 0)
{
lean_dec_ref(v___x_5419_);
lean_dec_ref(v_fixedParamPerms_5403_);
return v___x_5409_;
}
else
{
uint8_t v___x_5422_; 
v___x_5422_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5410_, v___x_5419_, v___x_5415_);
lean_dec_ref(v___x_5419_);
if (v___x_5422_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5403_);
return v___x_5409_;
}
else
{
if (v___x_5407_ == 0)
{
size_t v___x_5423_; size_t v___x_5424_; 
v___x_5423_ = ((size_t)1ULL);
v___x_5424_ = lean_usize_add(v_i_5405_, v___x_5423_);
v_i_5405_ = v___x_5424_;
goto _start;
}
else
{
lean_dec_ref(v_fixedParamPerms_5403_);
return v___x_5409_;
}
}
}
}
else
{
uint8_t v___x_5426_; 
lean_dec_ref(v_fixedParamPerms_5403_);
v___x_5426_ = 0;
return v___x_5426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5427_, lean_object* v_as_5428_, lean_object* v_i_5429_, lean_object* v_stop_5430_){
_start:
{
size_t v_i_boxed_5431_; size_t v_stop_boxed_5432_; uint8_t v_res_5433_; lean_object* v_r_5434_; 
v_i_boxed_5431_ = lean_unbox_usize(v_i_5429_);
lean_dec(v_i_5429_);
v_stop_boxed_5432_ = lean_unbox_usize(v_stop_5430_);
lean_dec(v_stop_5430_);
v_res_5433_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5427_, v_as_5428_, v_i_boxed_5431_, v_stop_boxed_5432_);
lean_dec_ref(v_as_5428_);
v_r_5434_ = lean_box(v_res_5433_);
return v_r_5434_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5435_){
_start:
{
lean_object* v_perms_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; uint8_t v___x_5439_; 
v_perms_5436_ = lean_ctor_get(v_fixedParamPerms_5435_, 1);
lean_inc_ref(v_perms_5436_);
v___x_5437_ = lean_unsigned_to_nat(0u);
v___x_5438_ = lean_array_get_size(v_perms_5436_);
v___x_5439_ = lean_nat_dec_lt(v___x_5437_, v___x_5438_);
if (v___x_5439_ == 0)
{
uint8_t v___x_5440_; 
lean_dec_ref(v_perms_5436_);
lean_dec_ref(v_fixedParamPerms_5435_);
v___x_5440_ = 1;
return v___x_5440_;
}
else
{
if (v___x_5439_ == 0)
{
lean_dec_ref(v_perms_5436_);
lean_dec_ref(v_fixedParamPerms_5435_);
return v___x_5439_;
}
else
{
size_t v___x_5441_; size_t v___x_5442_; uint8_t v___x_5443_; 
v___x_5441_ = ((size_t)0ULL);
v___x_5442_ = lean_usize_of_nat(v___x_5438_);
v___x_5443_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5435_, v_perms_5436_, v___x_5441_, v___x_5442_);
lean_dec_ref(v_perms_5436_);
if (v___x_5443_ == 0)
{
return v___x_5439_;
}
else
{
uint8_t v___x_5444_; 
v___x_5444_ = 0;
return v___x_5444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5445_){
_start:
{
uint8_t v_res_5446_; lean_object* v_r_5447_; 
v_res_5446_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5445_);
v_r_5447_ = lean_box(v_res_5446_);
return v_r_5447_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5448_, lean_object* v_ys_5449_, lean_object* v_hsz_5450_, lean_object* v_x_5451_, lean_object* v_x_5452_){
_start:
{
uint8_t v___x_5453_; 
v___x_5453_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5448_, v_ys_5449_, v_x_5451_);
return v___x_5453_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5454_, lean_object* v_ys_5455_, lean_object* v_hsz_5456_, lean_object* v_x_5457_, lean_object* v_x_5458_){
_start:
{
uint8_t v_res_5459_; lean_object* v_r_5460_; 
v_res_5459_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5454_, v_ys_5455_, v_hsz_5456_, v_x_5457_, v_x_5458_);
lean_dec_ref(v_ys_5455_);
lean_dec_ref(v_xs_5454_);
v_r_5460_ = lean_box(v_res_5459_);
return v_r_5460_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5461_; 
v___x_5461_ = l_Array_instInhabited(lean_box(0));
return v___x_5461_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5462_){
_start:
{
lean_object* v___f_5463_; lean_object* v___f_5464_; lean_object* v___f_5465_; lean_object* v___f_5466_; lean_object* v___f_5467_; lean_object* v___f_5468_; lean_object* v___f_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; 
v___f_5463_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5464_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5465_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5466_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5467_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5468_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5469_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5470_, 0, v___f_5463_);
lean_ctor_set(v___x_5470_, 1, v___f_5464_);
v___x_5471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5471_, 0, v___x_5470_);
lean_ctor_set(v___x_5471_, 1, v___f_5465_);
lean_ctor_set(v___x_5471_, 2, v___f_5466_);
lean_ctor_set(v___x_5471_, 3, v___f_5467_);
lean_ctor_set(v___x_5471_, 4, v___f_5468_);
v___x_5472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5472_, 0, v___x_5471_);
lean_ctor_set(v___x_5472_, 1, v___f_5469_);
v___x_5473_ = l_Lean_Elab_instInhabitedFixedParamPerms_default;
v___x_5474_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5475_, 0, v___x_5474_);
lean_ctor_set(v___x_5475_, 1, v___x_5474_);
v___x_5476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5476_, 0, v___x_5473_);
lean_ctor_set(v___x_5476_, 1, v___x_5475_);
v___x_5477_ = l_instInhabitedOfMonad___redArg(v___x_5472_, v___x_5476_);
v___x_5478_ = lean_panic_fn(v___x_5477_, v_msg_5462_);
return v___x_5478_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5479_; 
v___x_5479_ = l_Array_instInhabited(lean_box(0));
return v___x_5479_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5480_){
_start:
{
lean_object* v___f_5481_; lean_object* v___f_5482_; lean_object* v___f_5483_; lean_object* v___f_5484_; lean_object* v___f_5485_; lean_object* v___f_5486_; lean_object* v___f_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; 
v___f_5481_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5482_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5483_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5484_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5485_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5486_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5487_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5488_, 0, v___f_5481_);
lean_ctor_set(v___x_5488_, 1, v___f_5482_);
v___x_5489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5489_, 0, v___x_5488_);
lean_ctor_set(v___x_5489_, 1, v___f_5483_);
lean_ctor_set(v___x_5489_, 2, v___f_5484_);
lean_ctor_set(v___x_5489_, 3, v___f_5485_);
lean_ctor_set(v___x_5489_, 4, v___f_5486_);
v___x_5490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5490_, 0, v___x_5489_);
lean_ctor_set(v___x_5490_, 1, v___f_5487_);
v___x_5491_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5492_, 0, v___x_5491_);
v___x_5493_ = l_instInhabitedOfMonad___redArg(v___x_5490_, v___x_5492_);
v___x_5494_ = lean_panic_fn(v___x_5493_, v_msg_5480_);
return v___x_5494_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5495_, lean_object* v_a_5496_, lean_object* v_b_5497_){
_start:
{
lean_object* v_a_5499_; uint8_t v___x_5503_; 
v___x_5503_ = lean_nat_dec_lt(v_a_5496_, v_upperBound_5495_);
if (v___x_5503_ == 0)
{
lean_dec(v_a_5496_);
return v_b_5497_;
}
else
{
lean_object* v_snd_5504_; lean_object* v_snd_5505_; lean_object* v_snd_5506_; lean_object* v_snd_5507_; lean_object* v_fst_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5620_; 
v_snd_5504_ = lean_ctor_get(v_b_5497_, 1);
lean_inc(v_snd_5504_);
v_snd_5505_ = lean_ctor_get(v_snd_5504_, 1);
lean_inc(v_snd_5505_);
v_snd_5506_ = lean_ctor_get(v_snd_5505_, 1);
lean_inc(v_snd_5506_);
v_snd_5507_ = lean_ctor_get(v_snd_5506_, 1);
lean_inc(v_snd_5507_);
v_fst_5508_ = lean_ctor_get(v_b_5497_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v_b_5497_);
if (v_isSharedCheck_5620_ == 0)
{
lean_object* v_unused_5621_; 
v_unused_5621_ = lean_ctor_get(v_b_5497_, 1);
lean_dec(v_unused_5621_);
v___x_5510_ = v_b_5497_;
v_isShared_5511_ = v_isSharedCheck_5620_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_fst_5508_);
lean_dec(v_b_5497_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5620_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
lean_object* v_fst_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5618_; 
v_fst_5512_ = lean_ctor_get(v_snd_5504_, 0);
v_isSharedCheck_5618_ = !lean_is_exclusive(v_snd_5504_);
if (v_isSharedCheck_5618_ == 0)
{
lean_object* v_unused_5619_; 
v_unused_5619_ = lean_ctor_get(v_snd_5504_, 1);
lean_dec(v_unused_5619_);
v___x_5514_ = v_snd_5504_;
v_isShared_5515_ = v_isSharedCheck_5618_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_fst_5512_);
lean_dec(v_snd_5504_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5618_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v_fst_5516_; lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5616_; 
v_fst_5516_ = lean_ctor_get(v_snd_5505_, 0);
v_isSharedCheck_5616_ = !lean_is_exclusive(v_snd_5505_);
if (v_isSharedCheck_5616_ == 0)
{
lean_object* v_unused_5617_; 
v_unused_5617_ = lean_ctor_get(v_snd_5505_, 1);
lean_dec(v_unused_5617_);
v___x_5518_ = v_snd_5505_;
v_isShared_5519_ = v_isSharedCheck_5616_;
goto v_resetjp_5517_;
}
else
{
lean_inc(v_fst_5516_);
lean_dec(v_snd_5505_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5616_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v_fst_5520_; lean_object* v___x_5522_; uint8_t v_isShared_5523_; uint8_t v_isSharedCheck_5614_; 
v_fst_5520_ = lean_ctor_get(v_snd_5506_, 0);
v_isSharedCheck_5614_ = !lean_is_exclusive(v_snd_5506_);
if (v_isSharedCheck_5614_ == 0)
{
lean_object* v_unused_5615_; 
v_unused_5615_ = lean_ctor_get(v_snd_5506_, 1);
lean_dec(v_unused_5615_);
v___x_5522_ = v_snd_5506_;
v_isShared_5523_ = v_isSharedCheck_5614_;
goto v_resetjp_5521_;
}
else
{
lean_inc(v_fst_5520_);
lean_dec(v_snd_5506_);
v___x_5522_ = lean_box(0);
v_isShared_5523_ = v_isSharedCheck_5614_;
goto v_resetjp_5521_;
}
v_resetjp_5521_:
{
lean_object* v_array_5524_; lean_object* v_start_5525_; lean_object* v_stop_5526_; uint8_t v___x_5527_; 
v_array_5524_ = lean_ctor_get(v_snd_5507_, 0);
v_start_5525_ = lean_ctor_get(v_snd_5507_, 1);
v_stop_5526_ = lean_ctor_get(v_snd_5507_, 2);
v___x_5527_ = lean_nat_dec_lt(v_start_5525_, v_stop_5526_);
if (v___x_5527_ == 0)
{
lean_object* v___x_5529_; 
lean_dec(v_a_5496_);
if (v_isShared_5523_ == 0)
{
v___x_5529_ = v___x_5522_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_fst_5520_);
lean_ctor_set(v_reuseFailAlloc_5539_, 1, v_snd_5507_);
v___x_5529_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
lean_object* v___x_5531_; 
if (v_isShared_5519_ == 0)
{
lean_ctor_set(v___x_5518_, 1, v___x_5529_);
v___x_5531_ = v___x_5518_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_fst_5516_);
lean_ctor_set(v_reuseFailAlloc_5538_, 1, v___x_5529_);
v___x_5531_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
lean_object* v___x_5533_; 
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 1, v___x_5531_);
v___x_5533_ = v___x_5514_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_fst_5512_);
lean_ctor_set(v_reuseFailAlloc_5537_, 1, v___x_5531_);
v___x_5533_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
lean_object* v___x_5535_; 
if (v_isShared_5511_ == 0)
{
lean_ctor_set(v___x_5510_, 1, v___x_5533_);
v___x_5535_ = v___x_5510_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5536_; 
v_reuseFailAlloc_5536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_fst_5508_);
lean_ctor_set(v_reuseFailAlloc_5536_, 1, v___x_5533_);
v___x_5535_ = v_reuseFailAlloc_5536_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
return v___x_5535_;
}
}
}
}
}
else
{
lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5610_; 
lean_inc(v_stop_5526_);
lean_inc(v_start_5525_);
lean_inc_ref(v_array_5524_);
v_isSharedCheck_5610_ = !lean_is_exclusive(v_snd_5507_);
if (v_isSharedCheck_5610_ == 0)
{
lean_object* v_unused_5611_; lean_object* v_unused_5612_; lean_object* v_unused_5613_; 
v_unused_5611_ = lean_ctor_get(v_snd_5507_, 2);
lean_dec(v_unused_5611_);
v_unused_5612_ = lean_ctor_get(v_snd_5507_, 1);
lean_dec(v_unused_5612_);
v_unused_5613_ = lean_ctor_get(v_snd_5507_, 0);
lean_dec(v_unused_5613_);
v___x_5541_ = v_snd_5507_;
v_isShared_5542_ = v_isSharedCheck_5610_;
goto v_resetjp_5540_;
}
else
{
lean_dec(v_snd_5507_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5610_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v_array_5543_; lean_object* v_start_5544_; lean_object* v_stop_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5550_; 
v_array_5543_ = lean_ctor_get(v_fst_5520_, 0);
v_start_5544_ = lean_ctor_get(v_fst_5520_, 1);
v_stop_5545_ = lean_ctor_get(v_fst_5520_, 2);
v___x_5546_ = lean_array_fget(v_array_5524_, v_start_5525_);
v___x_5547_ = lean_unsigned_to_nat(1u);
v___x_5548_ = lean_nat_add(v_start_5525_, v___x_5547_);
lean_dec(v_start_5525_);
if (v_isShared_5542_ == 0)
{
lean_ctor_set(v___x_5541_, 1, v___x_5548_);
v___x_5550_ = v___x_5541_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_array_5524_);
lean_ctor_set(v_reuseFailAlloc_5609_, 1, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5609_, 2, v_stop_5526_);
v___x_5550_ = v_reuseFailAlloc_5609_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
uint8_t v___x_5551_; 
v___x_5551_ = lean_nat_dec_lt(v_start_5544_, v_stop_5545_);
if (v___x_5551_ == 0)
{
lean_object* v___x_5553_; 
lean_dec(v___x_5546_);
lean_dec(v_a_5496_);
if (v_isShared_5523_ == 0)
{
lean_ctor_set(v___x_5522_, 1, v___x_5550_);
v___x_5553_ = v___x_5522_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_fst_5520_);
lean_ctor_set(v_reuseFailAlloc_5563_, 1, v___x_5550_);
v___x_5553_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
lean_object* v___x_5555_; 
if (v_isShared_5519_ == 0)
{
lean_ctor_set(v___x_5518_, 1, v___x_5553_);
v___x_5555_ = v___x_5518_;
goto v_reusejp_5554_;
}
else
{
lean_object* v_reuseFailAlloc_5562_; 
v_reuseFailAlloc_5562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_fst_5516_);
lean_ctor_set(v_reuseFailAlloc_5562_, 1, v___x_5553_);
v___x_5555_ = v_reuseFailAlloc_5562_;
goto v_reusejp_5554_;
}
v_reusejp_5554_:
{
lean_object* v___x_5557_; 
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 1, v___x_5555_);
v___x_5557_ = v___x_5514_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_fst_5512_);
lean_ctor_set(v_reuseFailAlloc_5561_, 1, v___x_5555_);
v___x_5557_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
lean_object* v___x_5559_; 
if (v_isShared_5511_ == 0)
{
lean_ctor_set(v___x_5510_, 1, v___x_5557_);
v___x_5559_ = v___x_5510_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v_fst_5508_);
lean_ctor_set(v_reuseFailAlloc_5560_, 1, v___x_5557_);
v___x_5559_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
return v___x_5559_;
}
}
}
}
}
else
{
lean_object* v___x_5565_; uint8_t v_isShared_5566_; uint8_t v_isSharedCheck_5605_; 
lean_inc(v_stop_5545_);
lean_inc(v_start_5544_);
lean_inc_ref(v_array_5543_);
v_isSharedCheck_5605_ = !lean_is_exclusive(v_fst_5520_);
if (v_isSharedCheck_5605_ == 0)
{
lean_object* v_unused_5606_; lean_object* v_unused_5607_; lean_object* v_unused_5608_; 
v_unused_5606_ = lean_ctor_get(v_fst_5520_, 2);
lean_dec(v_unused_5606_);
v_unused_5607_ = lean_ctor_get(v_fst_5520_, 1);
lean_dec(v_unused_5607_);
v_unused_5608_ = lean_ctor_get(v_fst_5520_, 0);
lean_dec(v_unused_5608_);
v___x_5565_ = v_fst_5520_;
v_isShared_5566_ = v_isSharedCheck_5605_;
goto v_resetjp_5564_;
}
else
{
lean_dec(v_fst_5520_);
v___x_5565_ = lean_box(0);
v_isShared_5566_ = v_isSharedCheck_5605_;
goto v_resetjp_5564_;
}
v_resetjp_5564_:
{
lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5570_; 
v___x_5567_ = lean_array_fget(v_array_5543_, v_start_5544_);
v___x_5568_ = lean_nat_add(v_start_5544_, v___x_5547_);
lean_dec(v_start_5544_);
if (v_isShared_5566_ == 0)
{
lean_ctor_set(v___x_5565_, 1, v___x_5568_);
v___x_5570_ = v___x_5565_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v_array_5543_);
lean_ctor_set(v_reuseFailAlloc_5604_, 1, v___x_5568_);
lean_ctor_set(v_reuseFailAlloc_5604_, 2, v_stop_5545_);
v___x_5570_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
uint8_t v___x_5571_; 
v___x_5571_ = lean_unbox(v___x_5567_);
lean_dec(v___x_5567_);
if (v___x_5571_ == 0)
{
lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5577_; 
v___x_5572_ = lean_array_get_size(v_fst_5516_);
v___x_5573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5573_, 0, v___x_5572_);
v___x_5574_ = lean_array_push(v_fst_5508_, v___x_5573_);
v___x_5575_ = lean_array_push(v_fst_5516_, v___x_5546_);
if (v_isShared_5523_ == 0)
{
lean_ctor_set(v___x_5522_, 1, v___x_5550_);
lean_ctor_set(v___x_5522_, 0, v___x_5570_);
v___x_5577_ = v___x_5522_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v___x_5570_);
lean_ctor_set(v_reuseFailAlloc_5587_, 1, v___x_5550_);
v___x_5577_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
lean_object* v___x_5579_; 
if (v_isShared_5519_ == 0)
{
lean_ctor_set(v___x_5518_, 1, v___x_5577_);
lean_ctor_set(v___x_5518_, 0, v___x_5575_);
v___x_5579_ = v___x_5518_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v___x_5575_);
lean_ctor_set(v_reuseFailAlloc_5586_, 1, v___x_5577_);
v___x_5579_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
lean_object* v___x_5581_; 
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 1, v___x_5579_);
v___x_5581_ = v___x_5514_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_fst_5512_);
lean_ctor_set(v_reuseFailAlloc_5585_, 1, v___x_5579_);
v___x_5581_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
lean_object* v___x_5583_; 
if (v_isShared_5511_ == 0)
{
lean_ctor_set(v___x_5510_, 1, v___x_5581_);
lean_ctor_set(v___x_5510_, 0, v___x_5574_);
v___x_5583_ = v___x_5510_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v___x_5574_);
lean_ctor_set(v_reuseFailAlloc_5584_, 1, v___x_5581_);
v___x_5583_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
v_a_5499_ = v___x_5583_;
goto v___jp_5498_;
}
}
}
}
}
else
{
lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5593_; 
v___x_5588_ = lean_box(0);
v___x_5589_ = lean_array_push(v_fst_5508_, v___x_5588_);
v___x_5590_ = l_Lean_Expr_fvarId_x21(v___x_5546_);
lean_dec(v___x_5546_);
v___x_5591_ = lean_array_push(v_fst_5512_, v___x_5590_);
if (v_isShared_5523_ == 0)
{
lean_ctor_set(v___x_5522_, 1, v___x_5550_);
lean_ctor_set(v___x_5522_, 0, v___x_5570_);
v___x_5593_ = v___x_5522_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v___x_5570_);
lean_ctor_set(v_reuseFailAlloc_5603_, 1, v___x_5550_);
v___x_5593_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
lean_object* v___x_5595_; 
if (v_isShared_5519_ == 0)
{
lean_ctor_set(v___x_5518_, 1, v___x_5593_);
v___x_5595_ = v___x_5518_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_fst_5516_);
lean_ctor_set(v_reuseFailAlloc_5602_, 1, v___x_5593_);
v___x_5595_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
lean_object* v___x_5597_; 
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 1, v___x_5595_);
lean_ctor_set(v___x_5514_, 0, v___x_5591_);
v___x_5597_ = v___x_5514_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v___x_5591_);
lean_ctor_set(v_reuseFailAlloc_5601_, 1, v___x_5595_);
v___x_5597_ = v_reuseFailAlloc_5601_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
lean_object* v___x_5599_; 
if (v_isShared_5511_ == 0)
{
lean_ctor_set(v___x_5510_, 1, v___x_5597_);
lean_ctor_set(v___x_5510_, 0, v___x_5589_);
v___x_5599_ = v___x_5510_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5600_; 
v_reuseFailAlloc_5600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5600_, 0, v___x_5589_);
lean_ctor_set(v_reuseFailAlloc_5600_, 1, v___x_5597_);
v___x_5599_ = v_reuseFailAlloc_5600_;
goto v_reusejp_5598_;
}
v_reusejp_5598_:
{
v_a_5499_ = v___x_5599_;
goto v___jp_5498_;
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
v___jp_5498_:
{
lean_object* v___x_5500_; lean_object* v___x_5501_; 
v___x_5500_ = lean_unsigned_to_nat(1u);
v___x_5501_ = lean_nat_add(v_a_5496_, v___x_5500_);
lean_dec(v_a_5496_);
v_a_5496_ = v___x_5501_;
v_b_5497_ = v_a_5499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5622_, lean_object* v_a_5623_, lean_object* v_b_5624_){
_start:
{
lean_object* v_res_5625_; 
v_res_5625_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5622_, v_a_5623_, v_b_5624_);
lean_dec(v_upperBound_5622_);
return v_res_5625_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5626_, size_t v_i_5627_, size_t v_stop_5628_){
_start:
{
uint8_t v___x_5629_; 
v___x_5629_ = lean_usize_dec_eq(v_i_5627_, v_stop_5628_);
if (v___x_5629_ == 0)
{
uint8_t v___x_5630_; lean_object* v___x_5631_; uint8_t v___x_5632_; 
v___x_5630_ = 1;
v___x_5631_ = lean_array_uget_borrowed(v_as_5626_, v_i_5627_);
v___x_5632_ = l_Lean_Expr_isFVar(v___x_5631_);
if (v___x_5632_ == 0)
{
return v___x_5630_;
}
else
{
if (v___x_5629_ == 0)
{
size_t v___x_5633_; size_t v___x_5634_; 
v___x_5633_ = ((size_t)1ULL);
v___x_5634_ = lean_usize_add(v_i_5627_, v___x_5633_);
v_i_5627_ = v___x_5634_;
goto _start;
}
else
{
return v___x_5630_;
}
}
}
else
{
uint8_t v___x_5636_; 
v___x_5636_ = 0;
return v___x_5636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5637_, lean_object* v_i_5638_, lean_object* v_stop_5639_){
_start:
{
size_t v_i_boxed_5640_; size_t v_stop_boxed_5641_; uint8_t v_res_5642_; lean_object* v_r_5643_; 
v_i_boxed_5640_ = lean_unbox_usize(v_i_5638_);
lean_dec(v_i_5638_);
v_stop_boxed_5641_ = lean_unbox_usize(v_stop_5639_);
lean_dec(v_stop_5639_);
v_res_5642_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5637_, v_i_boxed_5640_, v_stop_boxed_5641_);
lean_dec_ref(v_as_5637_);
v_r_5643_ = lean_box(v_res_5642_);
return v_r_5643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5644_, size_t v_sz_5645_, size_t v_i_5646_, lean_object* v_bs_5647_){
_start:
{
uint8_t v___x_5648_; 
v___x_5648_ = lean_usize_dec_lt(v_i_5646_, v_sz_5645_);
if (v___x_5648_ == 0)
{
return v_bs_5647_;
}
else
{
lean_object* v_v_5649_; lean_object* v___x_5650_; lean_object* v_bs_x27_5651_; lean_object* v___y_5653_; 
v_v_5649_ = lean_array_uget(v_bs_5647_, v_i_5646_);
v___x_5650_ = lean_unsigned_to_nat(0u);
v_bs_x27_5651_ = lean_array_uset(v_bs_5647_, v_i_5646_, v___x_5650_);
if (lean_obj_tag(v_v_5649_) == 0)
{
v___y_5653_ = v_v_5649_;
goto v___jp_5652_;
}
else
{
lean_object* v_val_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; 
v_val_5658_ = lean_ctor_get(v_v_5649_, 0);
lean_inc(v_val_5658_);
lean_dec_ref(v_v_5649_);
v___x_5659_ = lean_box(0);
v___x_5660_ = lean_array_get_borrowed(v___x_5659_, v___x_5644_, v_val_5658_);
lean_dec(v_val_5658_);
lean_inc(v___x_5660_);
v___y_5653_ = v___x_5660_;
goto v___jp_5652_;
}
v___jp_5652_:
{
size_t v___x_5654_; size_t v___x_5655_; lean_object* v___x_5656_; 
v___x_5654_ = ((size_t)1ULL);
v___x_5655_ = lean_usize_add(v_i_5646_, v___x_5654_);
v___x_5656_ = lean_array_uset(v_bs_x27_5651_, v_i_5646_, v___y_5653_);
v_i_5646_ = v___x_5655_;
v_bs_5647_ = v___x_5656_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5661_, lean_object* v_sz_5662_, lean_object* v_i_5663_, lean_object* v_bs_5664_){
_start:
{
size_t v_sz_boxed_5665_; size_t v_i_boxed_5666_; lean_object* v_res_5667_; 
v_sz_boxed_5665_ = lean_unbox_usize(v_sz_5662_);
lean_dec(v_sz_5662_);
v_i_boxed_5666_ = lean_unbox_usize(v_i_5663_);
lean_dec(v_i_5663_);
v_res_5667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5661_, v_sz_boxed_5665_, v_i_boxed_5666_, v_bs_5664_);
lean_dec_ref(v___x_5661_);
return v_res_5667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5668_, size_t v_sz_5669_, size_t v_i_5670_, lean_object* v_bs_5671_){
_start:
{
uint8_t v___x_5672_; 
v___x_5672_ = lean_usize_dec_lt(v_i_5670_, v_sz_5669_);
if (v___x_5672_ == 0)
{
return v_bs_5671_;
}
else
{
lean_object* v_v_5673_; lean_object* v___x_5674_; lean_object* v_bs_x27_5675_; size_t v_sz_5676_; size_t v___x_5677_; lean_object* v___x_5678_; size_t v___x_5679_; size_t v___x_5680_; lean_object* v___x_5681_; 
v_v_5673_ = lean_array_uget(v_bs_5671_, v_i_5670_);
v___x_5674_ = lean_unsigned_to_nat(0u);
v_bs_x27_5675_ = lean_array_uset(v_bs_5671_, v_i_5670_, v___x_5674_);
v_sz_5676_ = lean_array_size(v_v_5673_);
v___x_5677_ = ((size_t)0ULL);
v___x_5678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5668_, v_sz_5676_, v___x_5677_, v_v_5673_);
v___x_5679_ = ((size_t)1ULL);
v___x_5680_ = lean_usize_add(v_i_5670_, v___x_5679_);
v___x_5681_ = lean_array_uset(v_bs_x27_5675_, v_i_5670_, v___x_5678_);
v_i_5670_ = v___x_5680_;
v_bs_5671_ = v___x_5681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5683_, lean_object* v_sz_5684_, lean_object* v_i_5685_, lean_object* v_bs_5686_){
_start:
{
size_t v_sz_boxed_5687_; size_t v_i_boxed_5688_; lean_object* v_res_5689_; 
v_sz_boxed_5687_ = lean_unbox_usize(v_sz_5684_);
lean_dec(v_sz_5684_);
v_i_boxed_5688_ = lean_unbox_usize(v_i_5685_);
lean_dec(v_i_5685_);
v_res_5689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5683_, v_sz_boxed_5687_, v_i_boxed_5688_, v_bs_5686_);
lean_dec_ref(v___x_5683_);
return v_res_5689_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; 
v___x_5692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5693_ = lean_unsigned_to_nat(6u);
v___x_5694_ = lean_unsigned_to_nat(463u);
v___x_5695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5696_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5697_ = l_mkPanicMessageWithDecl(v___x_5696_, v___x_5695_, v___x_5694_, v___x_5693_, v___x_5692_);
return v___x_5697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5698_, lean_object* v_as_5699_, size_t v_sz_5700_, size_t v_i_5701_, lean_object* v_b_5702_){
_start:
{
lean_object* v_a_5704_; uint8_t v___x_5708_; 
v___x_5708_ = lean_usize_dec_lt(v_i_5701_, v_sz_5700_);
if (v___x_5708_ == 0)
{
return v_b_5702_;
}
else
{
lean_object* v_a_5709_; lean_object* v___x_5710_; uint8_t v_changed_5711_; 
v_a_5709_ = lean_array_uget_borrowed(v_as_5699_, v_i_5701_);
v___x_5710_ = lean_array_get_size(v___x_5698_);
v_changed_5711_ = lean_nat_dec_lt(v_a_5709_, v___x_5710_);
if (v_changed_5711_ == 0)
{
lean_object* v___x_5712_; lean_object* v___x_5713_; 
lean_dec_ref(v_b_5702_);
v___x_5712_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5713_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5712_);
if (lean_obj_tag(v___x_5713_) == 0)
{
lean_object* v_a_5714_; 
v_a_5714_ = lean_ctor_get(v___x_5713_, 0);
lean_inc(v_a_5714_);
lean_dec_ref(v___x_5713_);
return v_a_5714_;
}
else
{
lean_object* v_a_5715_; 
v_a_5715_ = lean_ctor_get(v___x_5713_, 0);
lean_inc(v_a_5715_);
lean_dec_ref(v___x_5713_);
v_a_5704_ = v_a_5715_;
goto v___jp_5703_;
}
}
else
{
lean_object* v___x_5716_; lean_object* v___x_5717_; 
v___x_5716_ = lean_box(0);
v___x_5717_ = lean_array_get_borrowed(v___x_5716_, v___x_5698_, v_a_5709_);
if (lean_obj_tag(v___x_5717_) == 1)
{
lean_object* v_val_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; 
v_val_5718_ = lean_ctor_get(v___x_5717_, 0);
v___x_5719_ = lean_box(v_changed_5711_);
v___x_5720_ = lean_array_set(v_b_5702_, v_val_5718_, v___x_5719_);
v_a_5704_ = v___x_5720_;
goto v___jp_5703_;
}
else
{
v_a_5704_ = v_b_5702_;
goto v___jp_5703_;
}
}
}
v___jp_5703_:
{
size_t v___x_5705_; size_t v___x_5706_; 
v___x_5705_ = ((size_t)1ULL);
v___x_5706_ = lean_usize_add(v_i_5701_, v___x_5705_);
v_i_5701_ = v___x_5706_;
v_b_5702_ = v_a_5704_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5721_, lean_object* v_as_5722_, lean_object* v_sz_5723_, lean_object* v_i_5724_, lean_object* v_b_5725_){
_start:
{
size_t v_sz_boxed_5726_; size_t v_i_boxed_5727_; lean_object* v_res_5728_; 
v_sz_boxed_5726_ = lean_unbox_usize(v_sz_5723_);
lean_dec(v_sz_5723_);
v_i_boxed_5727_ = lean_unbox_usize(v_i_5724_);
lean_dec(v_i_5724_);
v_res_5728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5721_, v_as_5722_, v_sz_boxed_5726_, v_i_boxed_5727_, v_b_5725_);
lean_dec_ref(v_as_5722_);
lean_dec_ref(v___x_5721_);
return v_res_5728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5729_, lean_object* v_a_5730_, lean_object* v_b_5731_){
_start:
{
uint8_t v___x_5732_; 
v___x_5732_ = lean_nat_dec_lt(v_a_5730_, v_upperBound_5729_);
if (v___x_5732_ == 0)
{
lean_dec(v_a_5730_);
return v_b_5731_;
}
else
{
lean_object* v_snd_5733_; lean_object* v_snd_5734_; lean_object* v_fst_5735_; lean_object* v___x_5737_; uint8_t v_isShared_5738_; uint8_t v_isSharedCheck_5801_; 
v_snd_5733_ = lean_ctor_get(v_b_5731_, 1);
lean_inc(v_snd_5733_);
v_snd_5734_ = lean_ctor_get(v_snd_5733_, 1);
lean_inc(v_snd_5734_);
v_fst_5735_ = lean_ctor_get(v_b_5731_, 0);
v_isSharedCheck_5801_ = !lean_is_exclusive(v_b_5731_);
if (v_isSharedCheck_5801_ == 0)
{
lean_object* v_unused_5802_; 
v_unused_5802_ = lean_ctor_get(v_b_5731_, 1);
lean_dec(v_unused_5802_);
v___x_5737_ = v_b_5731_;
v_isShared_5738_ = v_isSharedCheck_5801_;
goto v_resetjp_5736_;
}
else
{
lean_inc(v_fst_5735_);
lean_dec(v_b_5731_);
v___x_5737_ = lean_box(0);
v_isShared_5738_ = v_isSharedCheck_5801_;
goto v_resetjp_5736_;
}
v_resetjp_5736_:
{
lean_object* v_fst_5739_; lean_object* v___x_5741_; uint8_t v_isShared_5742_; uint8_t v_isSharedCheck_5799_; 
v_fst_5739_ = lean_ctor_get(v_snd_5733_, 0);
v_isSharedCheck_5799_ = !lean_is_exclusive(v_snd_5733_);
if (v_isSharedCheck_5799_ == 0)
{
lean_object* v_unused_5800_; 
v_unused_5800_ = lean_ctor_get(v_snd_5733_, 1);
lean_dec(v_unused_5800_);
v___x_5741_ = v_snd_5733_;
v_isShared_5742_ = v_isSharedCheck_5799_;
goto v_resetjp_5740_;
}
else
{
lean_inc(v_fst_5739_);
lean_dec(v_snd_5733_);
v___x_5741_ = lean_box(0);
v_isShared_5742_ = v_isSharedCheck_5799_;
goto v_resetjp_5740_;
}
v_resetjp_5740_:
{
lean_object* v_array_5743_; lean_object* v_start_5744_; lean_object* v_stop_5745_; uint8_t v___x_5746_; 
v_array_5743_ = lean_ctor_get(v_snd_5734_, 0);
v_start_5744_ = lean_ctor_get(v_snd_5734_, 1);
v_stop_5745_ = lean_ctor_get(v_snd_5734_, 2);
v___x_5746_ = lean_nat_dec_lt(v_start_5744_, v_stop_5745_);
if (v___x_5746_ == 0)
{
lean_object* v___x_5748_; 
lean_dec(v_a_5730_);
if (v_isShared_5742_ == 0)
{
v___x_5748_ = v___x_5741_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_fst_5739_);
lean_ctor_set(v_reuseFailAlloc_5752_, 1, v_snd_5734_);
v___x_5748_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
lean_object* v___x_5750_; 
if (v_isShared_5738_ == 0)
{
lean_ctor_set(v___x_5737_, 1, v___x_5748_);
v___x_5750_ = v___x_5737_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_fst_5735_);
lean_ctor_set(v_reuseFailAlloc_5751_, 1, v___x_5748_);
v___x_5750_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
return v___x_5750_;
}
}
}
else
{
lean_object* v___x_5754_; uint8_t v_isShared_5755_; uint8_t v_isSharedCheck_5795_; 
lean_inc(v_stop_5745_);
lean_inc(v_start_5744_);
lean_inc_ref(v_array_5743_);
v_isSharedCheck_5795_ = !lean_is_exclusive(v_snd_5734_);
if (v_isSharedCheck_5795_ == 0)
{
lean_object* v_unused_5796_; lean_object* v_unused_5797_; lean_object* v_unused_5798_; 
v_unused_5796_ = lean_ctor_get(v_snd_5734_, 2);
lean_dec(v_unused_5796_);
v_unused_5797_ = lean_ctor_get(v_snd_5734_, 1);
lean_dec(v_unused_5797_);
v_unused_5798_ = lean_ctor_get(v_snd_5734_, 0);
lean_dec(v_unused_5798_);
v___x_5754_ = v_snd_5734_;
v_isShared_5755_ = v_isSharedCheck_5795_;
goto v_resetjp_5753_;
}
else
{
lean_dec(v_snd_5734_);
v___x_5754_ = lean_box(0);
v_isShared_5755_ = v_isSharedCheck_5795_;
goto v_resetjp_5753_;
}
v_resetjp_5753_:
{
lean_object* v_array_5756_; lean_object* v_start_5757_; lean_object* v_stop_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5763_; 
v_array_5756_ = lean_ctor_get(v_fst_5739_, 0);
v_start_5757_ = lean_ctor_get(v_fst_5739_, 1);
v_stop_5758_ = lean_ctor_get(v_fst_5739_, 2);
v___x_5759_ = lean_array_fget(v_array_5743_, v_start_5744_);
v___x_5760_ = lean_unsigned_to_nat(1u);
v___x_5761_ = lean_nat_add(v_start_5744_, v___x_5760_);
lean_dec(v_start_5744_);
if (v_isShared_5755_ == 0)
{
lean_ctor_set(v___x_5754_, 1, v___x_5761_);
v___x_5763_ = v___x_5754_;
goto v_reusejp_5762_;
}
else
{
lean_object* v_reuseFailAlloc_5794_; 
v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_array_5743_);
lean_ctor_set(v_reuseFailAlloc_5794_, 1, v___x_5761_);
lean_ctor_set(v_reuseFailAlloc_5794_, 2, v_stop_5745_);
v___x_5763_ = v_reuseFailAlloc_5794_;
goto v_reusejp_5762_;
}
v_reusejp_5762_:
{
uint8_t v___x_5764_; 
v___x_5764_ = lean_nat_dec_lt(v_start_5757_, v_stop_5758_);
if (v___x_5764_ == 0)
{
lean_object* v___x_5766_; 
lean_dec(v___x_5759_);
lean_dec(v_a_5730_);
if (v_isShared_5742_ == 0)
{
lean_ctor_set(v___x_5741_, 1, v___x_5763_);
v___x_5766_ = v___x_5741_;
goto v_reusejp_5765_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v_fst_5739_);
lean_ctor_set(v_reuseFailAlloc_5770_, 1, v___x_5763_);
v___x_5766_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5765_;
}
v_reusejp_5765_:
{
lean_object* v___x_5768_; 
if (v_isShared_5738_ == 0)
{
lean_ctor_set(v___x_5737_, 1, v___x_5766_);
v___x_5768_ = v___x_5737_;
goto v_reusejp_5767_;
}
else
{
lean_object* v_reuseFailAlloc_5769_; 
v_reuseFailAlloc_5769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5769_, 0, v_fst_5735_);
lean_ctor_set(v_reuseFailAlloc_5769_, 1, v___x_5766_);
v___x_5768_ = v_reuseFailAlloc_5769_;
goto v_reusejp_5767_;
}
v_reusejp_5767_:
{
return v___x_5768_;
}
}
}
else
{
lean_object* v___x_5772_; uint8_t v_isShared_5773_; uint8_t v_isSharedCheck_5790_; 
lean_inc(v_stop_5758_);
lean_inc(v_start_5757_);
lean_inc_ref(v_array_5756_);
v_isSharedCheck_5790_ = !lean_is_exclusive(v_fst_5739_);
if (v_isSharedCheck_5790_ == 0)
{
lean_object* v_unused_5791_; lean_object* v_unused_5792_; lean_object* v_unused_5793_; 
v_unused_5791_ = lean_ctor_get(v_fst_5739_, 2);
lean_dec(v_unused_5791_);
v_unused_5792_ = lean_ctor_get(v_fst_5739_, 1);
lean_dec(v_unused_5792_);
v_unused_5793_ = lean_ctor_get(v_fst_5739_, 0);
lean_dec(v_unused_5793_);
v___x_5772_ = v_fst_5739_;
v_isShared_5773_ = v_isSharedCheck_5790_;
goto v_resetjp_5771_;
}
else
{
lean_dec(v_fst_5739_);
v___x_5772_ = lean_box(0);
v_isShared_5773_ = v_isSharedCheck_5790_;
goto v_resetjp_5771_;
}
v_resetjp_5771_:
{
lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5777_; 
v___x_5774_ = lean_array_fget(v_array_5756_, v_start_5757_);
v___x_5775_ = lean_nat_add(v_start_5757_, v___x_5760_);
lean_dec(v_start_5757_);
if (v_isShared_5773_ == 0)
{
lean_ctor_set(v___x_5772_, 1, v___x_5775_);
v___x_5777_ = v___x_5772_;
goto v_reusejp_5776_;
}
else
{
lean_object* v_reuseFailAlloc_5789_; 
v_reuseFailAlloc_5789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5789_, 0, v_array_5756_);
lean_ctor_set(v_reuseFailAlloc_5789_, 1, v___x_5775_);
lean_ctor_set(v_reuseFailAlloc_5789_, 2, v_stop_5758_);
v___x_5777_ = v_reuseFailAlloc_5789_;
goto v_reusejp_5776_;
}
v_reusejp_5776_:
{
size_t v_sz_5778_; size_t v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5782_; 
v_sz_5778_ = lean_array_size(v___x_5774_);
v___x_5779_ = ((size_t)0ULL);
v___x_5780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5759_, v___x_5774_, v_sz_5778_, v___x_5779_, v_fst_5735_);
lean_dec(v___x_5774_);
lean_dec(v___x_5759_);
if (v_isShared_5742_ == 0)
{
lean_ctor_set(v___x_5741_, 1, v___x_5763_);
lean_ctor_set(v___x_5741_, 0, v___x_5777_);
v___x_5782_ = v___x_5741_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5788_; 
v_reuseFailAlloc_5788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5788_, 0, v___x_5777_);
lean_ctor_set(v_reuseFailAlloc_5788_, 1, v___x_5763_);
v___x_5782_ = v_reuseFailAlloc_5788_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
lean_object* v___x_5784_; 
if (v_isShared_5738_ == 0)
{
lean_ctor_set(v___x_5737_, 1, v___x_5782_);
lean_ctor_set(v___x_5737_, 0, v___x_5780_);
v___x_5784_ = v___x_5737_;
goto v_reusejp_5783_;
}
else
{
lean_object* v_reuseFailAlloc_5787_; 
v_reuseFailAlloc_5787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5787_, 0, v___x_5780_);
lean_ctor_set(v_reuseFailAlloc_5787_, 1, v___x_5782_);
v___x_5784_ = v_reuseFailAlloc_5787_;
goto v_reusejp_5783_;
}
v_reusejp_5783_:
{
lean_object* v___x_5785_; 
v___x_5785_ = lean_nat_add(v_a_5730_, v___x_5760_);
lean_dec(v_a_5730_);
v_a_5730_ = v___x_5785_;
v_b_5731_ = v___x_5784_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_5803_, lean_object* v_a_5804_, lean_object* v_b_5805_){
_start:
{
lean_object* v_res_5806_; 
v_res_5806_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_5803_, v_a_5804_, v_b_5805_);
lean_dec(v_upperBound_5803_);
return v_res_5806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5807_, uint8_t v___x_5808_, lean_object* v_as_5809_, size_t v_sz_5810_, size_t v_i_5811_, lean_object* v_b_5812_){
_start:
{
lean_object* v_a_5814_; uint8_t v___x_5818_; 
v___x_5818_ = lean_usize_dec_lt(v_i_5811_, v_sz_5810_);
if (v___x_5818_ == 0)
{
return v_b_5812_;
}
else
{
lean_object* v_fst_5819_; lean_object* v_snd_5820_; lean_object* v___x_5822_; uint8_t v_isShared_5823_; uint8_t v_isSharedCheck_5841_; 
v_fst_5819_ = lean_ctor_get(v_b_5812_, 0);
v_snd_5820_ = lean_ctor_get(v_b_5812_, 1);
v_isSharedCheck_5841_ = !lean_is_exclusive(v_b_5812_);
if (v_isSharedCheck_5841_ == 0)
{
v___x_5822_ = v_b_5812_;
v_isShared_5823_ = v_isSharedCheck_5841_;
goto v_resetjp_5821_;
}
else
{
lean_inc(v_snd_5820_);
lean_inc(v_fst_5819_);
lean_dec(v_b_5812_);
v___x_5822_ = lean_box(0);
v_isShared_5823_ = v_isSharedCheck_5841_;
goto v_resetjp_5821_;
}
v_resetjp_5821_:
{
lean_object* v_a_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; 
v_a_5828_ = lean_array_uget_borrowed(v_as_5809_, v_i_5811_);
v___x_5829_ = lean_box(0);
v___x_5830_ = lean_array_get_borrowed(v___x_5829_, v___x_5807_, v_a_5828_);
if (lean_obj_tag(v___x_5830_) == 1)
{
lean_object* v_val_5831_; uint8_t v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; uint8_t v___x_5835_; 
v_val_5831_ = lean_ctor_get(v___x_5830_, 0);
v___x_5832_ = 0;
v___x_5833_ = lean_box(v___x_5832_);
v___x_5834_ = lean_array_get_borrowed(v___x_5833_, v_fst_5819_, v_val_5831_);
v___x_5835_ = lean_unbox(v___x_5834_);
if (v___x_5835_ == 0)
{
if (v___x_5808_ == 0)
{
goto v___jp_5824_;
}
else
{
lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; 
lean_del_object(v___x_5822_);
lean_dec(v_snd_5820_);
v___x_5836_ = lean_box(v___x_5808_);
v___x_5837_ = lean_array_set(v_fst_5819_, v_val_5831_, v___x_5836_);
v___x_5838_ = lean_box(v___x_5808_);
v___x_5839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5839_, 0, v___x_5837_);
lean_ctor_set(v___x_5839_, 1, v___x_5838_);
v_a_5814_ = v___x_5839_;
goto v___jp_5813_;
}
}
else
{
goto v___jp_5824_;
}
}
else
{
lean_object* v___x_5840_; 
lean_del_object(v___x_5822_);
v___x_5840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5840_, 0, v_fst_5819_);
lean_ctor_set(v___x_5840_, 1, v_snd_5820_);
v_a_5814_ = v___x_5840_;
goto v___jp_5813_;
}
v___jp_5824_:
{
lean_object* v___x_5826_; 
if (v_isShared_5823_ == 0)
{
v___x_5826_ = v___x_5822_;
goto v_reusejp_5825_;
}
else
{
lean_object* v_reuseFailAlloc_5827_; 
v_reuseFailAlloc_5827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5827_, 0, v_fst_5819_);
lean_ctor_set(v_reuseFailAlloc_5827_, 1, v_snd_5820_);
v___x_5826_ = v_reuseFailAlloc_5827_;
goto v_reusejp_5825_;
}
v_reusejp_5825_:
{
v_a_5814_ = v___x_5826_;
goto v___jp_5813_;
}
}
}
}
v___jp_5813_:
{
size_t v___x_5815_; size_t v___x_5816_; 
v___x_5815_ = ((size_t)1ULL);
v___x_5816_ = lean_usize_add(v_i_5811_, v___x_5815_);
v_i_5811_ = v___x_5816_;
v_b_5812_ = v_a_5814_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5842_, lean_object* v___x_5843_, lean_object* v_as_5844_, lean_object* v_sz_5845_, lean_object* v_i_5846_, lean_object* v_b_5847_){
_start:
{
uint8_t v___x_8469__boxed_5848_; size_t v_sz_boxed_5849_; size_t v_i_boxed_5850_; lean_object* v_res_5851_; 
v___x_8469__boxed_5848_ = lean_unbox(v___x_5843_);
v_sz_boxed_5849_ = lean_unbox_usize(v_sz_5845_);
lean_dec(v_sz_5845_);
v_i_boxed_5850_ = lean_unbox_usize(v_i_5846_);
lean_dec(v_i_5846_);
v_res_5851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5842_, v___x_8469__boxed_5848_, v_as_5844_, v_sz_boxed_5849_, v_i_boxed_5850_, v_b_5847_);
lean_dec_ref(v_as_5844_);
lean_dec_ref(v___x_5842_);
return v_res_5851_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5852_, lean_object* v___x_5853_, lean_object* v_fixedParamPerms_5854_, lean_object* v_next_5855_, lean_object* v_a_5856_, lean_object* v_b_5857_){
_start:
{
lean_object* v_a_5859_; uint8_t v___x_5863_; 
v___x_5863_ = lean_nat_dec_lt(v_a_5856_, v_upperBound_5852_);
if (v___x_5863_ == 0)
{
lean_dec(v_a_5856_);
return v_b_5857_;
}
else
{
lean_object* v_fst_5864_; lean_object* v_snd_5865_; lean_object* v___x_5867_; uint8_t v_isShared_5868_; uint8_t v_isSharedCheck_5901_; 
v_fst_5864_ = lean_ctor_get(v_b_5857_, 0);
v_snd_5865_ = lean_ctor_get(v_b_5857_, 1);
v_isSharedCheck_5901_ = !lean_is_exclusive(v_b_5857_);
if (v_isSharedCheck_5901_ == 0)
{
v___x_5867_ = v_b_5857_;
v_isShared_5868_ = v_isSharedCheck_5901_;
goto v_resetjp_5866_;
}
else
{
lean_inc(v_snd_5865_);
lean_inc(v_fst_5864_);
lean_dec(v_b_5857_);
v___x_5867_ = lean_box(0);
v_isShared_5868_ = v_isSharedCheck_5901_;
goto v_resetjp_5866_;
}
v_resetjp_5866_:
{
lean_object* v___x_5869_; 
v___x_5869_ = lean_array_fget_borrowed(v___x_5853_, v_a_5856_);
if (lean_obj_tag(v___x_5869_) == 1)
{
lean_object* v_val_5870_; uint8_t v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; uint8_t v___x_5874_; 
v_val_5870_ = lean_ctor_get(v___x_5869_, 0);
v___x_5871_ = 0;
v___x_5872_ = lean_box(v___x_5871_);
v___x_5873_ = lean_array_get_borrowed(v___x_5872_, v_fst_5864_, v_val_5870_);
v___x_5874_ = lean_unbox(v___x_5873_);
if (v___x_5874_ == 0)
{
lean_object* v___x_5876_; 
if (v_isShared_5868_ == 0)
{
v___x_5876_ = v___x_5867_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_fst_5864_);
lean_ctor_set(v_reuseFailAlloc_5877_, 1, v_snd_5865_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
v_a_5859_ = v___x_5876_;
goto v___jp_5858_;
}
}
else
{
lean_object* v_revDeps_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5883_; 
lean_inc(v___x_5873_);
v_revDeps_5878_ = lean_ctor_get(v_fixedParamPerms_5854_, 2);
v___x_5879_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_5880_ = lean_array_get_borrowed(v___x_5879_, v_revDeps_5878_, v_next_5855_);
v___x_5881_ = lean_array_get_borrowed(v___x_5879_, v___x_5880_, v_a_5856_);
if (v_isShared_5868_ == 0)
{
v___x_5883_ = v___x_5867_;
goto v_reusejp_5882_;
}
else
{
lean_object* v_reuseFailAlloc_5897_; 
v_reuseFailAlloc_5897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5897_, 0, v_fst_5864_);
lean_ctor_set(v_reuseFailAlloc_5897_, 1, v_snd_5865_);
v___x_5883_ = v_reuseFailAlloc_5897_;
goto v_reusejp_5882_;
}
v_reusejp_5882_:
{
size_t v_sz_5884_; size_t v___x_5885_; uint8_t v___x_5886_; lean_object* v___x_5887_; lean_object* v_fst_5888_; lean_object* v_snd_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5896_; 
v_sz_5884_ = lean_array_size(v___x_5881_);
v___x_5885_ = ((size_t)0ULL);
v___x_5886_ = lean_unbox(v___x_5873_);
lean_dec(v___x_5873_);
v___x_5887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5853_, v___x_5886_, v___x_5881_, v_sz_5884_, v___x_5885_, v___x_5883_);
v_fst_5888_ = lean_ctor_get(v___x_5887_, 0);
v_snd_5889_ = lean_ctor_get(v___x_5887_, 1);
v_isSharedCheck_5896_ = !lean_is_exclusive(v___x_5887_);
if (v_isSharedCheck_5896_ == 0)
{
v___x_5891_ = v___x_5887_;
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_snd_5889_);
lean_inc(v_fst_5888_);
lean_dec(v___x_5887_);
v___x_5891_ = lean_box(0);
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
v_resetjp_5890_:
{
lean_object* v___x_5894_; 
if (v_isShared_5892_ == 0)
{
v___x_5894_ = v___x_5891_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_fst_5888_);
lean_ctor_set(v_reuseFailAlloc_5895_, 1, v_snd_5889_);
v___x_5894_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
v_a_5859_ = v___x_5894_;
goto v___jp_5858_;
}
}
}
}
}
else
{
lean_object* v___x_5899_; 
if (v_isShared_5868_ == 0)
{
v___x_5899_ = v___x_5867_;
goto v_reusejp_5898_;
}
else
{
lean_object* v_reuseFailAlloc_5900_; 
v_reuseFailAlloc_5900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5900_, 0, v_fst_5864_);
lean_ctor_set(v_reuseFailAlloc_5900_, 1, v_snd_5865_);
v___x_5899_ = v_reuseFailAlloc_5900_;
goto v_reusejp_5898_;
}
v_reusejp_5898_:
{
v_a_5859_ = v___x_5899_;
goto v___jp_5858_;
}
}
}
}
v___jp_5858_:
{
lean_object* v___x_5860_; lean_object* v___x_5861_; 
v___x_5860_ = lean_unsigned_to_nat(1u);
v___x_5861_ = lean_nat_add(v_a_5856_, v___x_5860_);
lean_dec(v_a_5856_);
v_a_5856_ = v___x_5861_;
v_b_5857_ = v_a_5859_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5902_, lean_object* v___x_5903_, lean_object* v_fixedParamPerms_5904_, lean_object* v_next_5905_, lean_object* v_a_5906_, lean_object* v_b_5907_){
_start:
{
lean_object* v_res_5908_; 
v_res_5908_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5902_, v___x_5903_, v_fixedParamPerms_5904_, v_next_5905_, v_a_5906_, v_b_5907_);
lean_dec(v_next_5905_);
lean_dec_ref(v_fixedParamPerms_5904_);
lean_dec_ref(v___x_5903_);
lean_dec(v_upperBound_5902_);
return v_res_5908_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5909_, lean_object* v___x_5910_, lean_object* v_fixedParamPerms_5911_, lean_object* v_a_5912_, lean_object* v_b_5913_){
_start:
{
uint8_t v___x_5914_; 
v___x_5914_ = lean_nat_dec_lt(v_a_5912_, v_upperBound_5909_);
if (v___x_5914_ == 0)
{
lean_dec(v_a_5912_);
return v_b_5913_;
}
else
{
lean_object* v_fst_5915_; lean_object* v_snd_5916_; lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_5939_; 
v_fst_5915_ = lean_ctor_get(v_b_5913_, 0);
v_snd_5916_ = lean_ctor_get(v_b_5913_, 1);
v_isSharedCheck_5939_ = !lean_is_exclusive(v_b_5913_);
if (v_isSharedCheck_5939_ == 0)
{
v___x_5918_ = v_b_5913_;
v_isShared_5919_ = v_isSharedCheck_5939_;
goto v_resetjp_5917_;
}
else
{
lean_inc(v_snd_5916_);
lean_inc(v_fst_5915_);
lean_dec(v_b_5913_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_5939_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5924_; 
v___x_5920_ = lean_array_fget_borrowed(v___x_5910_, v_a_5912_);
v___x_5921_ = lean_array_get_size(v___x_5920_);
v___x_5922_ = lean_unsigned_to_nat(0u);
if (v_isShared_5919_ == 0)
{
v___x_5924_ = v___x_5918_;
goto v_reusejp_5923_;
}
else
{
lean_object* v_reuseFailAlloc_5938_; 
v_reuseFailAlloc_5938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5938_, 0, v_fst_5915_);
lean_ctor_set(v_reuseFailAlloc_5938_, 1, v_snd_5916_);
v___x_5924_ = v_reuseFailAlloc_5938_;
goto v_reusejp_5923_;
}
v_reusejp_5923_:
{
lean_object* v___x_5925_; lean_object* v_fst_5926_; lean_object* v_snd_5927_; lean_object* v___x_5929_; uint8_t v_isShared_5930_; uint8_t v_isSharedCheck_5937_; 
v___x_5925_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5921_, v___x_5920_, v_fixedParamPerms_5911_, v_a_5912_, v___x_5922_, v___x_5924_);
v_fst_5926_ = lean_ctor_get(v___x_5925_, 0);
v_snd_5927_ = lean_ctor_get(v___x_5925_, 1);
v_isSharedCheck_5937_ = !lean_is_exclusive(v___x_5925_);
if (v_isSharedCheck_5937_ == 0)
{
v___x_5929_ = v___x_5925_;
v_isShared_5930_ = v_isSharedCheck_5937_;
goto v_resetjp_5928_;
}
else
{
lean_inc(v_snd_5927_);
lean_inc(v_fst_5926_);
lean_dec(v___x_5925_);
v___x_5929_ = lean_box(0);
v_isShared_5930_ = v_isSharedCheck_5937_;
goto v_resetjp_5928_;
}
v_resetjp_5928_:
{
lean_object* v___x_5932_; 
if (v_isShared_5930_ == 0)
{
v___x_5932_ = v___x_5929_;
goto v_reusejp_5931_;
}
else
{
lean_object* v_reuseFailAlloc_5936_; 
v_reuseFailAlloc_5936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5936_, 0, v_fst_5926_);
lean_ctor_set(v_reuseFailAlloc_5936_, 1, v_snd_5927_);
v___x_5932_ = v_reuseFailAlloc_5936_;
goto v_reusejp_5931_;
}
v_reusejp_5931_:
{
lean_object* v___x_5933_; lean_object* v___x_5934_; 
v___x_5933_ = lean_unsigned_to_nat(1u);
v___x_5934_ = lean_nat_add(v_a_5912_, v___x_5933_);
lean_dec(v_a_5912_);
v_a_5912_ = v___x_5934_;
v_b_5913_ = v___x_5932_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5940_, lean_object* v___x_5941_, lean_object* v_fixedParamPerms_5942_, lean_object* v_a_5943_, lean_object* v_b_5944_){
_start:
{
lean_object* v_res_5945_; 
v_res_5945_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5940_, v___x_5941_, v_fixedParamPerms_5942_, v_a_5943_, v_b_5944_);
lean_dec_ref(v_fixedParamPerms_5942_);
lean_dec_ref(v___x_5941_);
lean_dec(v_upperBound_5940_);
return v_res_5945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_5946_, lean_object* v___x_5947_, lean_object* v_fixedParamPerms_5948_, lean_object* v_b_5949_){
_start:
{
lean_object* v_snd_5950_; uint8_t v___x_5951_; 
v_snd_5950_ = lean_ctor_get(v_b_5949_, 1);
v___x_5951_ = lean_unbox(v_snd_5950_);
if (v___x_5951_ == 0)
{
lean_object* v_fst_5952_; lean_object* v___x_5954_; uint8_t v_isShared_5955_; uint8_t v_isSharedCheck_5959_; 
lean_inc(v_snd_5950_);
v_fst_5952_ = lean_ctor_get(v_b_5949_, 0);
v_isSharedCheck_5959_ = !lean_is_exclusive(v_b_5949_);
if (v_isSharedCheck_5959_ == 0)
{
lean_object* v_unused_5960_; 
v_unused_5960_ = lean_ctor_get(v_b_5949_, 1);
lean_dec(v_unused_5960_);
v___x_5954_ = v_b_5949_;
v_isShared_5955_ = v_isSharedCheck_5959_;
goto v_resetjp_5953_;
}
else
{
lean_inc(v_fst_5952_);
lean_dec(v_b_5949_);
v___x_5954_ = lean_box(0);
v_isShared_5955_ = v_isSharedCheck_5959_;
goto v_resetjp_5953_;
}
v_resetjp_5953_:
{
lean_object* v___x_5957_; 
if (v_isShared_5955_ == 0)
{
v___x_5957_ = v___x_5954_;
goto v_reusejp_5956_;
}
else
{
lean_object* v_reuseFailAlloc_5958_; 
v_reuseFailAlloc_5958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5958_, 0, v_fst_5952_);
lean_ctor_set(v_reuseFailAlloc_5958_, 1, v_snd_5950_);
v___x_5957_ = v_reuseFailAlloc_5958_;
goto v_reusejp_5956_;
}
v_reusejp_5956_:
{
return v___x_5957_;
}
}
}
else
{
lean_object* v_fst_5961_; lean_object* v___x_5963_; uint8_t v_isShared_5964_; uint8_t v_isSharedCheck_5982_; 
v_fst_5961_ = lean_ctor_get(v_b_5949_, 0);
v_isSharedCheck_5982_ = !lean_is_exclusive(v_b_5949_);
if (v_isSharedCheck_5982_ == 0)
{
lean_object* v_unused_5983_; 
v_unused_5983_ = lean_ctor_get(v_b_5949_, 1);
lean_dec(v_unused_5983_);
v___x_5963_ = v_b_5949_;
v_isShared_5964_ = v_isSharedCheck_5982_;
goto v_resetjp_5962_;
}
else
{
lean_inc(v_fst_5961_);
lean_dec(v_b_5949_);
v___x_5963_ = lean_box(0);
v_isShared_5964_ = v_isSharedCheck_5982_;
goto v_resetjp_5962_;
}
v_resetjp_5962_:
{
uint8_t v_changed_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5969_; 
v_changed_5965_ = 0;
v___x_5966_ = lean_unsigned_to_nat(0u);
v___x_5967_ = lean_box(v_changed_5965_);
if (v_isShared_5964_ == 0)
{
lean_ctor_set(v___x_5963_, 1, v___x_5967_);
v___x_5969_ = v___x_5963_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5981_; 
v_reuseFailAlloc_5981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5981_, 0, v_fst_5961_);
lean_ctor_set(v_reuseFailAlloc_5981_, 1, v___x_5967_);
v___x_5969_ = v_reuseFailAlloc_5981_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
lean_object* v___x_5970_; lean_object* v_fst_5971_; lean_object* v_snd_5972_; lean_object* v___x_5974_; uint8_t v_isShared_5975_; uint8_t v_isSharedCheck_5980_; 
v___x_5970_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5946_, v___x_5947_, v_fixedParamPerms_5948_, v___x_5966_, v___x_5969_);
v_fst_5971_ = lean_ctor_get(v___x_5970_, 0);
v_snd_5972_ = lean_ctor_get(v___x_5970_, 1);
v_isSharedCheck_5980_ = !lean_is_exclusive(v___x_5970_);
if (v_isSharedCheck_5980_ == 0)
{
v___x_5974_ = v___x_5970_;
v_isShared_5975_ = v_isSharedCheck_5980_;
goto v_resetjp_5973_;
}
else
{
lean_inc(v_snd_5972_);
lean_inc(v_fst_5971_);
lean_dec(v___x_5970_);
v___x_5974_ = lean_box(0);
v_isShared_5975_ = v_isSharedCheck_5980_;
goto v_resetjp_5973_;
}
v_resetjp_5973_:
{
lean_object* v___x_5977_; 
if (v_isShared_5975_ == 0)
{
v___x_5977_ = v___x_5974_;
goto v_reusejp_5976_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v_fst_5971_);
lean_ctor_set(v_reuseFailAlloc_5979_, 1, v_snd_5972_);
v___x_5977_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5976_;
}
v_reusejp_5976_:
{
v_b_5949_ = v___x_5977_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_5984_, lean_object* v___x_5985_, lean_object* v_fixedParamPerms_5986_, lean_object* v_b_5987_){
_start:
{
lean_object* v_res_5988_; 
v_res_5988_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_5984_, v___x_5985_, v_fixedParamPerms_5986_, v_b_5987_);
lean_dec_ref(v_fixedParamPerms_5986_);
lean_dec_ref(v___x_5985_);
lean_dec(v___x_5984_);
return v_res_5988_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; 
v___x_5990_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_5991_ = lean_unsigned_to_nat(2u);
v___x_5992_ = lean_unsigned_to_nat(457u);
v___x_5993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5994_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5995_ = l_mkPanicMessageWithDecl(v___x_5994_, v___x_5993_, v___x_5992_, v___x_5991_, v___x_5990_);
return v___x_5995_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; 
v___x_5997_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_5998_ = lean_unsigned_to_nat(2u);
v___x_5999_ = lean_unsigned_to_nat(458u);
v___x_6000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6001_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6002_ = l_mkPanicMessageWithDecl(v___x_6001_, v___x_6000_, v___x_5999_, v___x_5998_, v___x_5997_);
return v___x_6002_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; 
v___x_6004_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_6005_ = lean_unsigned_to_nat(2u);
v___x_6006_ = lean_unsigned_to_nat(456u);
v___x_6007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6008_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6009_ = l_mkPanicMessageWithDecl(v___x_6008_, v___x_6007_, v___x_6006_, v___x_6005_, v___x_6004_);
return v___x_6009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6010_, lean_object* v_xs_6011_, lean_object* v_toErase_6012_){
_start:
{
lean_object* v___x_6013_; lean_object* v___x_6014_; uint8_t v___x_6098_; 
v___x_6013_ = lean_unsigned_to_nat(0u);
v___x_6014_ = lean_array_get_size(v_xs_6011_);
v___x_6098_ = lean_nat_dec_lt(v___x_6013_, v___x_6014_);
if (v___x_6098_ == 0)
{
goto v___jp_6015_;
}
else
{
if (v___x_6098_ == 0)
{
goto v___jp_6015_;
}
else
{
size_t v___x_6099_; size_t v___x_6100_; uint8_t v___x_6101_; 
v___x_6099_ = ((size_t)0ULL);
v___x_6100_ = lean_usize_of_nat(v___x_6014_);
v___x_6101_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6011_, v___x_6099_, v___x_6100_);
if (v___x_6101_ == 0)
{
goto v___jp_6015_;
}
else
{
lean_object* v___x_6102_; lean_object* v___x_6103_; 
lean_dec_ref(v_toErase_6012_);
lean_dec_ref(v_xs_6011_);
lean_dec_ref(v_fixedParamPerms_6010_);
v___x_6102_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6103_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6102_);
return v___x_6103_;
}
}
}
v___jp_6015_:
{
lean_object* v_numFixed_6016_; lean_object* v_perms_6017_; lean_object* v_revDeps_6018_; uint8_t v___x_6019_; 
v_numFixed_6016_ = lean_ctor_get(v_fixedParamPerms_6010_, 0);
v_perms_6017_ = lean_ctor_get(v_fixedParamPerms_6010_, 1);
lean_inc_ref(v_perms_6017_);
v_revDeps_6018_ = lean_ctor_get(v_fixedParamPerms_6010_, 2);
lean_inc_ref(v_revDeps_6018_);
v___x_6019_ = lean_nat_dec_eq(v_numFixed_6016_, v___x_6014_);
if (v___x_6019_ == 0)
{
lean_object* v___x_6020_; lean_object* v___x_6021_; 
lean_dec_ref(v_revDeps_6018_);
lean_dec_ref(v_perms_6017_);
lean_dec_ref(v_toErase_6012_);
lean_dec_ref(v_xs_6011_);
lean_dec_ref(v_fixedParamPerms_6010_);
v___x_6020_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6021_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6020_);
return v___x_6021_;
}
else
{
lean_object* v___x_6022_; lean_object* v___x_6023_; uint8_t v_changed_6024_; 
v___x_6022_ = lean_array_get_size(v_toErase_6012_);
v___x_6023_ = lean_array_get_size(v_perms_6017_);
v_changed_6024_ = lean_nat_dec_eq(v___x_6022_, v___x_6023_);
if (v_changed_6024_ == 0)
{
lean_object* v___x_6025_; lean_object* v___x_6026_; 
lean_dec_ref(v_revDeps_6018_);
lean_dec_ref(v_perms_6017_);
lean_dec_ref(v_toErase_6012_);
lean_dec_ref(v_xs_6011_);
lean_dec_ref(v_fixedParamPerms_6010_);
v___x_6025_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6026_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6025_);
return v___x_6026_;
}
else
{
uint8_t v_changed_6027_; lean_object* v___x_6028_; lean_object* v_mask_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v_fst_6035_; lean_object* v___x_6037_; uint8_t v_isShared_6038_; uint8_t v_isSharedCheck_6096_; 
v_changed_6027_ = 0;
v___x_6028_ = lean_box(v_changed_6027_);
lean_inc(v_numFixed_6016_);
v_mask_6029_ = lean_mk_array(v_numFixed_6016_, v___x_6028_);
v___x_6030_ = l_Array_toSubarray___redArg(v_toErase_6012_, v___x_6013_, v___x_6022_);
lean_inc_ref(v_perms_6017_);
v___x_6031_ = l_Array_toSubarray___redArg(v_perms_6017_, v___x_6013_, v___x_6023_);
v___x_6032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6030_);
lean_ctor_set(v___x_6032_, 1, v___x_6031_);
v___x_6033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6033_, 0, v_mask_6029_);
lean_ctor_set(v___x_6033_, 1, v___x_6032_);
v___x_6034_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6022_, v___x_6013_, v___x_6033_);
v_fst_6035_ = lean_ctor_get(v___x_6034_, 0);
v_isSharedCheck_6096_ = !lean_is_exclusive(v___x_6034_);
if (v_isSharedCheck_6096_ == 0)
{
lean_object* v_unused_6097_; 
v_unused_6097_ = lean_ctor_get(v___x_6034_, 1);
lean_dec(v_unused_6097_);
v___x_6037_ = v___x_6034_;
v_isShared_6038_ = v_isSharedCheck_6096_;
goto v_resetjp_6036_;
}
else
{
lean_inc(v_fst_6035_);
lean_dec(v___x_6034_);
v___x_6037_ = lean_box(0);
v_isShared_6038_ = v_isSharedCheck_6096_;
goto v_resetjp_6036_;
}
v_resetjp_6036_:
{
lean_object* v___x_6039_; lean_object* v___x_6041_; 
v___x_6039_ = lean_box(v_changed_6024_);
if (v_isShared_6038_ == 0)
{
lean_ctor_set(v___x_6037_, 1, v___x_6039_);
v___x_6041_ = v___x_6037_;
goto v_reusejp_6040_;
}
else
{
lean_object* v_reuseFailAlloc_6095_; 
v_reuseFailAlloc_6095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6095_, 0, v_fst_6035_);
lean_ctor_set(v_reuseFailAlloc_6095_, 1, v___x_6039_);
v___x_6041_ = v_reuseFailAlloc_6095_;
goto v_reusejp_6040_;
}
v_reusejp_6040_:
{
lean_object* v___x_6042_; lean_object* v___x_6044_; uint8_t v_isShared_6045_; uint8_t v_isSharedCheck_6091_; 
v___x_6042_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6023_, v_perms_6017_, v_fixedParamPerms_6010_, v___x_6041_);
v_isSharedCheck_6091_ = !lean_is_exclusive(v_fixedParamPerms_6010_);
if (v_isSharedCheck_6091_ == 0)
{
lean_object* v_unused_6092_; lean_object* v_unused_6093_; lean_object* v_unused_6094_; 
v_unused_6092_ = lean_ctor_get(v_fixedParamPerms_6010_, 2);
lean_dec(v_unused_6092_);
v_unused_6093_ = lean_ctor_get(v_fixedParamPerms_6010_, 1);
lean_dec(v_unused_6093_);
v_unused_6094_ = lean_ctor_get(v_fixedParamPerms_6010_, 0);
lean_dec(v_unused_6094_);
v___x_6044_ = v_fixedParamPerms_6010_;
v_isShared_6045_ = v_isSharedCheck_6091_;
goto v_resetjp_6043_;
}
else
{
lean_dec(v_fixedParamPerms_6010_);
v___x_6044_ = lean_box(0);
v_isShared_6045_ = v_isSharedCheck_6091_;
goto v_resetjp_6043_;
}
v_resetjp_6043_:
{
lean_object* v_fst_6046_; lean_object* v___x_6048_; uint8_t v_isShared_6049_; uint8_t v_isSharedCheck_6089_; 
v_fst_6046_ = lean_ctor_get(v___x_6042_, 0);
v_isSharedCheck_6089_ = !lean_is_exclusive(v___x_6042_);
if (v_isSharedCheck_6089_ == 0)
{
lean_object* v_unused_6090_; 
v_unused_6090_ = lean_ctor_get(v___x_6042_, 1);
lean_dec(v_unused_6090_);
v___x_6048_ = v___x_6042_;
v_isShared_6049_ = v_isSharedCheck_6089_;
goto v_resetjp_6047_;
}
else
{
lean_inc(v_fst_6046_);
lean_dec(v___x_6042_);
v___x_6048_ = lean_box(0);
v_isShared_6049_ = v_isSharedCheck_6089_;
goto v_resetjp_6047_;
}
v_resetjp_6047_:
{
lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6055_; 
v___x_6050_ = lean_array_get_size(v_fst_6046_);
v___x_6051_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6052_ = l_Array_toSubarray___redArg(v_fst_6046_, v___x_6013_, v___x_6050_);
v___x_6053_ = l_Array_toSubarray___redArg(v_xs_6011_, v___x_6013_, v___x_6014_);
if (v_isShared_6049_ == 0)
{
lean_ctor_set(v___x_6048_, 1, v___x_6053_);
lean_ctor_set(v___x_6048_, 0, v___x_6052_);
v___x_6055_ = v___x_6048_;
goto v_reusejp_6054_;
}
else
{
lean_object* v_reuseFailAlloc_6088_; 
v_reuseFailAlloc_6088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6088_, 0, v___x_6052_);
lean_ctor_set(v_reuseFailAlloc_6088_, 1, v___x_6053_);
v___x_6055_ = v_reuseFailAlloc_6088_;
goto v_reusejp_6054_;
}
v_reusejp_6054_:
{
lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v_snd_6060_; lean_object* v_snd_6061_; lean_object* v_fst_6062_; lean_object* v_fst_6063_; lean_object* v___x_6065_; uint8_t v_isShared_6066_; uint8_t v_isSharedCheck_6086_; 
v___x_6056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6056_, 0, v___x_6051_);
lean_ctor_set(v___x_6056_, 1, v___x_6055_);
v___x_6057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6051_);
lean_ctor_set(v___x_6057_, 1, v___x_6056_);
v___x_6058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6051_);
lean_ctor_set(v___x_6058_, 1, v___x_6057_);
v___x_6059_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6050_, v___x_6013_, v___x_6058_);
v_snd_6060_ = lean_ctor_get(v___x_6059_, 1);
lean_inc(v_snd_6060_);
v_snd_6061_ = lean_ctor_get(v_snd_6060_, 1);
lean_inc(v_snd_6061_);
v_fst_6062_ = lean_ctor_get(v___x_6059_, 0);
lean_inc(v_fst_6062_);
lean_dec_ref(v___x_6059_);
v_fst_6063_ = lean_ctor_get(v_snd_6060_, 0);
v_isSharedCheck_6086_ = !lean_is_exclusive(v_snd_6060_);
if (v_isSharedCheck_6086_ == 0)
{
lean_object* v_unused_6087_; 
v_unused_6087_ = lean_ctor_get(v_snd_6060_, 1);
lean_dec(v_unused_6087_);
v___x_6065_ = v_snd_6060_;
v_isShared_6066_ = v_isSharedCheck_6086_;
goto v_resetjp_6064_;
}
else
{
lean_inc(v_fst_6063_);
lean_dec(v_snd_6060_);
v___x_6065_ = lean_box(0);
v_isShared_6066_ = v_isSharedCheck_6086_;
goto v_resetjp_6064_;
}
v_resetjp_6064_:
{
lean_object* v_fst_6067_; lean_object* v___x_6069_; uint8_t v_isShared_6070_; uint8_t v_isSharedCheck_6084_; 
v_fst_6067_ = lean_ctor_get(v_snd_6061_, 0);
v_isSharedCheck_6084_ = !lean_is_exclusive(v_snd_6061_);
if (v_isSharedCheck_6084_ == 0)
{
lean_object* v_unused_6085_; 
v_unused_6085_ = lean_ctor_get(v_snd_6061_, 1);
lean_dec(v_unused_6085_);
v___x_6069_ = v_snd_6061_;
v_isShared_6070_ = v_isSharedCheck_6084_;
goto v_resetjp_6068_;
}
else
{
lean_inc(v_fst_6067_);
lean_dec(v_snd_6061_);
v___x_6069_ = lean_box(0);
v_isShared_6070_ = v_isSharedCheck_6084_;
goto v_resetjp_6068_;
}
v_resetjp_6068_:
{
lean_object* v___x_6071_; size_t v_sz_6072_; size_t v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6076_; 
v___x_6071_ = lean_array_get_size(v_fst_6067_);
v_sz_6072_ = lean_array_size(v_perms_6017_);
v___x_6073_ = ((size_t)0ULL);
v___x_6074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6062_, v_sz_6072_, v___x_6073_, v_perms_6017_);
lean_dec(v_fst_6062_);
if (v_isShared_6045_ == 0)
{
lean_ctor_set(v___x_6044_, 1, v___x_6074_);
lean_ctor_set(v___x_6044_, 0, v___x_6071_);
v___x_6076_ = v___x_6044_;
goto v_reusejp_6075_;
}
else
{
lean_object* v_reuseFailAlloc_6083_; 
v_reuseFailAlloc_6083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6083_, 0, v___x_6071_);
lean_ctor_set(v_reuseFailAlloc_6083_, 1, v___x_6074_);
lean_ctor_set(v_reuseFailAlloc_6083_, 2, v_revDeps_6018_);
v___x_6076_ = v_reuseFailAlloc_6083_;
goto v_reusejp_6075_;
}
v_reusejp_6075_:
{
lean_object* v___x_6078_; 
if (v_isShared_6070_ == 0)
{
lean_ctor_set(v___x_6069_, 1, v_fst_6063_);
v___x_6078_ = v___x_6069_;
goto v_reusejp_6077_;
}
else
{
lean_object* v_reuseFailAlloc_6082_; 
v_reuseFailAlloc_6082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6082_, 0, v_fst_6067_);
lean_ctor_set(v_reuseFailAlloc_6082_, 1, v_fst_6063_);
v___x_6078_ = v_reuseFailAlloc_6082_;
goto v_reusejp_6077_;
}
v_reusejp_6077_:
{
lean_object* v___x_6080_; 
if (v_isShared_6066_ == 0)
{
lean_ctor_set(v___x_6065_, 1, v___x_6078_);
lean_ctor_set(v___x_6065_, 0, v___x_6076_);
v___x_6080_ = v___x_6065_;
goto v_reusejp_6079_;
}
else
{
lean_object* v_reuseFailAlloc_6081_; 
v_reuseFailAlloc_6081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6081_, 0, v___x_6076_);
lean_ctor_set(v_reuseFailAlloc_6081_, 1, v___x_6078_);
v___x_6080_ = v_reuseFailAlloc_6081_;
goto v_reusejp_6079_;
}
v_reusejp_6079_:
{
return v___x_6080_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6104_, lean_object* v___x_6105_, lean_object* v_fixedParamPerms_6106_, lean_object* v_next_6107_, lean_object* v_inst_6108_, lean_object* v_R_6109_, lean_object* v_a_6110_, lean_object* v_b_6111_, lean_object* v_c_6112_){
_start:
{
lean_object* v___x_6113_; 
v___x_6113_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6104_, v___x_6105_, v_fixedParamPerms_6106_, v_next_6107_, v_a_6110_, v_b_6111_);
return v___x_6113_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6114_, lean_object* v___x_6115_, lean_object* v_fixedParamPerms_6116_, lean_object* v_next_6117_, lean_object* v_inst_6118_, lean_object* v_R_6119_, lean_object* v_a_6120_, lean_object* v_b_6121_, lean_object* v_c_6122_){
_start:
{
lean_object* v_res_6123_; 
v_res_6123_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6114_, v___x_6115_, v_fixedParamPerms_6116_, v_next_6117_, v_inst_6118_, v_R_6119_, v_a_6120_, v_b_6121_, v_c_6122_);
lean_dec(v_next_6117_);
lean_dec_ref(v_fixedParamPerms_6116_);
lean_dec_ref(v___x_6115_);
lean_dec(v_upperBound_6114_);
return v_res_6123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6124_, lean_object* v___x_6125_, lean_object* v_fixedParamPerms_6126_, lean_object* v_inst_6127_, lean_object* v_R_6128_, lean_object* v_a_6129_, lean_object* v_b_6130_, lean_object* v_c_6131_){
_start:
{
lean_object* v___x_6132_; 
v___x_6132_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6124_, v___x_6125_, v_fixedParamPerms_6126_, v_a_6129_, v_b_6130_);
return v___x_6132_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6133_, lean_object* v___x_6134_, lean_object* v_fixedParamPerms_6135_, lean_object* v_inst_6136_, lean_object* v_R_6137_, lean_object* v_a_6138_, lean_object* v_b_6139_, lean_object* v_c_6140_){
_start:
{
lean_object* v_res_6141_; 
v_res_6141_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6133_, v___x_6134_, v_fixedParamPerms_6135_, v_inst_6136_, v_R_6137_, v_a_6138_, v_b_6139_, v_c_6140_);
lean_dec_ref(v_fixedParamPerms_6135_);
lean_dec_ref(v___x_6134_);
lean_dec(v_upperBound_6133_);
return v_res_6141_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6142_, lean_object* v_inst_6143_, lean_object* v_R_6144_, lean_object* v_a_6145_, lean_object* v_b_6146_, lean_object* v_c_6147_){
_start:
{
lean_object* v___x_6148_; 
v___x_6148_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6142_, v_a_6145_, v_b_6146_);
return v___x_6148_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6149_, lean_object* v_inst_6150_, lean_object* v_R_6151_, lean_object* v_a_6152_, lean_object* v_b_6153_, lean_object* v_c_6154_){
_start:
{
lean_object* v_res_6155_; 
v_res_6155_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6149_, v_inst_6150_, v_R_6151_, v_a_6152_, v_b_6153_, v_c_6154_);
lean_dec(v_upperBound_6149_);
return v_res_6155_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6156_, lean_object* v_inst_6157_, lean_object* v_R_6158_, lean_object* v_a_6159_, lean_object* v_b_6160_, lean_object* v_c_6161_){
_start:
{
lean_object* v___x_6162_; 
v___x_6162_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6156_, v_a_6159_, v_b_6160_);
return v___x_6162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6163_, lean_object* v_inst_6164_, lean_object* v_R_6165_, lean_object* v_a_6166_, lean_object* v_b_6167_, lean_object* v_c_6168_){
_start:
{
lean_object* v_res_6169_; 
v_res_6169_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6163_, v_inst_6164_, v_R_6165_, v_a_6166_, v_b_6167_, v_c_6168_);
lean_dec(v_upperBound_6163_);
return v_res_6169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6227_; uint8_t v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; 
v___x_6227_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6228_ = 0;
v___x_6229_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6230_ = l_Lean_registerTraceClass(v___x_6227_, v___x_6228_, v___x_6229_);
return v___x_6230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6231_){
_start:
{
lean_object* v_res_6232_; 
v_res_6232_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6232_;
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
l_Lean_Elab_instInhabitedFixedParamPerms_default = _init_l_Lean_Elab_instInhabitedFixedParamPerms_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedFixedParamPerms_default);
l_Lean_Elab_instInhabitedFixedParamPerms = _init_l_Lean_Elab_instInhabitedFixedParamPerms();
lean_mark_persistent(l_Lean_Elab_instInhabitedFixedParamPerms);
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
