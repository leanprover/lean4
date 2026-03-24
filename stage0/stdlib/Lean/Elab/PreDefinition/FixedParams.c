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
lean_object* v___f_1042_; lean_object* v___x_30012__overap_1043_; lean_object* v___x_1044_; 
v___f_1042_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_30012__overap_1043_ = lean_panic_fn(v___f_1042_, v_msg_1036_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
v___x_1044_ = lean_apply_5(v___x_30012__overap_1043_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, lean_box(0));
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___boxed(lean_object* v_msg_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v_msg_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
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
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_bs_1072_);
return v___x_1079_;
}
else
{
lean_object* v_v_1080_; lean_object* v_value_1081_; lean_object* v___x_1082_; 
v_v_1080_ = lean_array_uget_borrowed(v_bs_1072_, v_i_1071_);
v_value_1081_ = lean_ctor_get(v_v_1080_, 7);
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
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
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
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v___y_1265_);
v___x_1272_ = lean_apply_7(v_k_1264_, v_b_1266_, v___y_1265_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, lean_box(0));
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed(lean_object* v_k_1273_, lean_object* v___y_1274_, lean_object* v_b_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(v_k_1273_, v___y_1274_, v_b_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1274_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(lean_object* v_name_1282_, uint8_t v_bi_1283_, lean_object* v_type_1284_, lean_object* v_k_1285_, uint8_t v_kind_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___f_1293_; lean_object* v___x_1294_; 
lean_inc(v___y_1287_);
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
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
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
lean_inc(v___y_1337_);
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
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
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
lean_object* v___y_1413_; lean_object* v_fileName_1422_; lean_object* v_fileMap_1423_; lean_object* v_options_1424_; lean_object* v_currRecDepth_1425_; lean_object* v_maxRecDepth_1426_; lean_object* v_ref_1427_; lean_object* v_currNamespace_1428_; lean_object* v_openDecls_1429_; lean_object* v_initHeartbeats_1430_; lean_object* v_maxHeartbeats_1431_; lean_object* v_quotContext_1432_; lean_object* v_currMacroScope_1433_; uint8_t v_diag_1434_; lean_object* v_cancelTk_x3f_1435_; uint8_t v_suppressElabErrors_1436_; lean_object* v_inheritedTraceOptions_1437_; uint8_t v___x_1438_; 
v_fileName_1422_ = lean_ctor_get(v___y_1409_, 0);
lean_inc_ref(v_fileName_1422_);
v_fileMap_1423_ = lean_ctor_get(v___y_1409_, 1);
lean_inc_ref(v_fileMap_1423_);
v_options_1424_ = lean_ctor_get(v___y_1409_, 2);
lean_inc_ref(v_options_1424_);
v_currRecDepth_1425_ = lean_ctor_get(v___y_1409_, 3);
lean_inc(v_currRecDepth_1425_);
v_maxRecDepth_1426_ = lean_ctor_get(v___y_1409_, 4);
lean_inc(v_maxRecDepth_1426_);
v_ref_1427_ = lean_ctor_get(v___y_1409_, 5);
lean_inc(v_ref_1427_);
v_currNamespace_1428_ = lean_ctor_get(v___y_1409_, 6);
lean_inc(v_currNamespace_1428_);
v_openDecls_1429_ = lean_ctor_get(v___y_1409_, 7);
lean_inc(v_openDecls_1429_);
v_initHeartbeats_1430_ = lean_ctor_get(v___y_1409_, 8);
lean_inc(v_initHeartbeats_1430_);
v_maxHeartbeats_1431_ = lean_ctor_get(v___y_1409_, 9);
lean_inc(v_maxHeartbeats_1431_);
v_quotContext_1432_ = lean_ctor_get(v___y_1409_, 10);
lean_inc(v_quotContext_1432_);
v_currMacroScope_1433_ = lean_ctor_get(v___y_1409_, 11);
lean_inc(v_currMacroScope_1433_);
v_diag_1434_ = lean_ctor_get_uint8(v___y_1409_, sizeof(void*)*14);
v_cancelTk_x3f_1435_ = lean_ctor_get(v___y_1409_, 12);
lean_inc(v_cancelTk_x3f_1435_);
v_suppressElabErrors_1436_ = lean_ctor_get_uint8(v___y_1409_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1437_ = lean_ctor_get(v___y_1409_, 13);
lean_inc_ref(v_inheritedTraceOptions_1437_);
lean_dec_ref(v___y_1409_);
v___x_1438_ = lean_nat_dec_eq(v_currRecDepth_1425_, v_maxRecDepth_1426_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1439_ = lean_unsigned_to_nat(1u);
v___x_1440_ = lean_nat_add(v_currRecDepth_1425_, v___x_1439_);
lean_dec(v_currRecDepth_1425_);
v___x_1441_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1441_, 0, v_fileName_1422_);
lean_ctor_set(v___x_1441_, 1, v_fileMap_1423_);
lean_ctor_set(v___x_1441_, 2, v_options_1424_);
lean_ctor_set(v___x_1441_, 3, v___x_1440_);
lean_ctor_set(v___x_1441_, 4, v_maxRecDepth_1426_);
lean_ctor_set(v___x_1441_, 5, v_ref_1427_);
lean_ctor_set(v___x_1441_, 6, v_currNamespace_1428_);
lean_ctor_set(v___x_1441_, 7, v_openDecls_1429_);
lean_ctor_set(v___x_1441_, 8, v_initHeartbeats_1430_);
lean_ctor_set(v___x_1441_, 9, v_maxHeartbeats_1431_);
lean_ctor_set(v___x_1441_, 10, v_quotContext_1432_);
lean_ctor_set(v___x_1441_, 11, v_currMacroScope_1433_);
lean_ctor_set(v___x_1441_, 12, v_cancelTk_x3f_1435_);
lean_ctor_set(v___x_1441_, 13, v_inheritedTraceOptions_1437_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*14, v_diag_1434_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*14 + 1, v_suppressElabErrors_1436_);
lean_inc(v___y_1410_);
lean_inc(v___y_1408_);
lean_inc_ref(v___y_1407_);
lean_inc(v___y_1406_);
v___x_1442_ = lean_apply_6(v_x_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___x_1441_, v___y_1410_, lean_box(0));
v___y_1413_ = v___x_1442_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1443_; 
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
lean_dec_ref(v_x_1405_);
v___x_1443_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1427_);
v___y_1413_ = v___x_1443_;
goto v___jp_1412_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object* v_a_1452_, lean_object* v_x_1453_){
_start:
{
if (lean_obj_tag(v_x_1453_) == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_box(0);
return v___x_1454_;
}
else
{
lean_object* v_key_1455_; lean_object* v_value_1456_; lean_object* v_tail_1457_; uint8_t v___x_1458_; 
v_key_1455_ = lean_ctor_get(v_x_1453_, 0);
v_value_1456_ = lean_ctor_get(v_x_1453_, 1);
v_tail_1457_ = lean_ctor_get(v_x_1453_, 2);
v___x_1458_ = l_Lean_ExprStructEq_beq(v_key_1455_, v_a_1452_);
if (v___x_1458_ == 0)
{
v_x_1453_ = v_tail_1457_;
goto _start;
}
else
{
lean_object* v___x_1460_; 
lean_inc(v_value_1456_);
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_value_1456_);
return v___x_1460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object* v_a_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1461_, v_x_1462_);
lean_dec(v_x_1462_);
lean_dec_ref(v_a_1461_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_m_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_buckets_1466_; lean_object* v___x_1467_; uint64_t v___x_1468_; uint64_t v___x_1469_; uint64_t v___x_1470_; uint64_t v_fold_1471_; uint64_t v___x_1472_; uint64_t v___x_1473_; uint64_t v___x_1474_; size_t v___x_1475_; size_t v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_buckets_1466_ = lean_ctor_get(v_m_1464_, 1);
v___x_1467_ = lean_array_get_size(v_buckets_1466_);
v___x_1468_ = l_Lean_ExprStructEq_hash(v_a_1465_);
v___x_1469_ = 32ULL;
v___x_1470_ = lean_uint64_shift_right(v___x_1468_, v___x_1469_);
v_fold_1471_ = lean_uint64_xor(v___x_1468_, v___x_1470_);
v___x_1472_ = 16ULL;
v___x_1473_ = lean_uint64_shift_right(v_fold_1471_, v___x_1472_);
v___x_1474_ = lean_uint64_xor(v_fold_1471_, v___x_1473_);
v___x_1475_ = lean_uint64_to_usize(v___x_1474_);
v___x_1476_ = lean_usize_of_nat(v___x_1467_);
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_sub(v___x_1476_, v___x_1477_);
v___x_1479_ = lean_usize_land(v___x_1475_, v___x_1478_);
v___x_1480_ = lean_array_uget_borrowed(v_buckets_1466_, v___x_1479_);
v___x_1481_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1465_, v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_m_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_1482_, v_a_1483_);
lean_dec_ref(v_a_1483_);
lean_dec_ref(v_m_1482_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1487_, lean_object* v_pre_1488_, lean_object* v_post_1489_, uint8_t v_usedLetOnly_1490_, uint8_t v_skipConstInApp_1491_, uint8_t v_skipInstances_1492_, lean_object* v_body_1493_, lean_object* v_x_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_array_push(v_fvars_1487_, v_x_1494_);
v___x_1502_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1488_, v_post_1489_, v_usedLetOnly_1490_, v_skipConstInApp_1491_, v_skipInstances_1492_, v___x_1501_, v_body_1493_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1503_, lean_object* v_pre_1504_, lean_object* v_post_1505_, lean_object* v_usedLetOnly_1506_, lean_object* v_skipConstInApp_1507_, lean_object* v_skipInstances_1508_, lean_object* v_body_1509_, lean_object* v_x_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
uint8_t v_usedLetOnly_boxed_1517_; uint8_t v_skipConstInApp_boxed_1518_; uint8_t v_skipInstances_boxed_1519_; lean_object* v_res_1520_; 
v_usedLetOnly_boxed_1517_ = lean_unbox(v_usedLetOnly_1506_);
v_skipConstInApp_boxed_1518_ = lean_unbox(v_skipConstInApp_1507_);
v_skipInstances_boxed_1519_ = lean_unbox(v_skipInstances_1508_);
v_res_1520_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1503_, v_pre_1504_, v_post_1505_, v_usedLetOnly_boxed_1517_, v_skipConstInApp_boxed_1518_, v_skipInstances_boxed_1519_, v_body_1509_, v_x_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1521_, lean_object* v_post_1522_, uint8_t v_usedLetOnly_1523_, uint8_t v_skipConstInApp_1524_, uint8_t v_skipInstances_1525_, lean_object* v_e_1526_, lean_object* v_a_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; 
lean_inc_ref(v_post_1522_);
lean_inc(v___y_1531_);
lean_inc_ref(v___y_1530_);
lean_inc(v___y_1529_);
lean_inc_ref(v___y_1528_);
lean_inc_ref(v_e_1526_);
v___x_1533_ = lean_apply_6(v_post_1522_, v_e_1526_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, lean_box(0));
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1552_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1552_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1552_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
switch(lean_obj_tag(v_a_1534_))
{
case 0:
{
lean_object* v_e_1538_; lean_object* v___x_1540_; 
lean_dec_ref(v_e_1526_);
lean_dec_ref(v_post_1522_);
lean_dec_ref(v_pre_1521_);
v_e_1538_ = lean_ctor_get(v_a_1534_, 0);
lean_inc_ref(v_e_1538_);
lean_dec_ref(v_a_1534_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v_e_1538_);
v___x_1540_ = v___x_1536_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_e_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
case 1:
{
lean_object* v_e_1542_; lean_object* v___x_1543_; 
lean_del_object(v___x_1536_);
lean_dec_ref(v_e_1526_);
v_e_1542_ = lean_ctor_get(v_a_1534_, 0);
lean_inc_ref(v_e_1542_);
lean_dec_ref(v_a_1534_);
v___x_1543_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1521_, v_post_1522_, v_usedLetOnly_1523_, v_skipConstInApp_1524_, v_skipInstances_1525_, v_e_1542_, v_a_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
return v___x_1543_;
}
default: 
{
lean_object* v_e_x3f_1544_; 
lean_dec_ref(v_post_1522_);
lean_dec_ref(v_pre_1521_);
v_e_x3f_1544_ = lean_ctor_get(v_a_1534_, 0);
lean_inc(v_e_x3f_1544_);
lean_dec_ref(v_a_1534_);
if (lean_obj_tag(v_e_x3f_1544_) == 0)
{
lean_object* v___x_1546_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v_e_1526_);
v___x_1546_ = v___x_1536_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_e_1526_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
else
{
lean_object* v_val_1548_; lean_object* v___x_1550_; 
lean_dec_ref(v_e_1526_);
v_val_1548_ = lean_ctor_get(v_e_x3f_1544_, 0);
lean_inc(v_val_1548_);
lean_dec_ref(v_e_x3f_1544_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v_val_1548_);
v___x_1550_ = v___x_1536_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_val_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref(v_e_1526_);
lean_dec_ref(v_post_1522_);
lean_dec_ref(v_pre_1521_);
v_a_1553_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1533_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1533_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1561_, lean_object* v_post_1562_, uint8_t v_usedLetOnly_1563_, uint8_t v_skipConstInApp_1564_, uint8_t v_skipInstances_1565_, lean_object* v_fvars_1566_, lean_object* v_e_1567_, lean_object* v_a_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
if (lean_obj_tag(v_e_1567_) == 6)
{
lean_object* v_binderName_1574_; lean_object* v_binderType_1575_; lean_object* v_body_1576_; uint8_t v_binderInfo_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_binderName_1574_ = lean_ctor_get(v_e_1567_, 0);
lean_inc(v_binderName_1574_);
v_binderType_1575_ = lean_ctor_get(v_e_1567_, 1);
lean_inc_ref(v_binderType_1575_);
v_body_1576_ = lean_ctor_get(v_e_1567_, 2);
lean_inc_ref(v_body_1576_);
v_binderInfo_1577_ = lean_ctor_get_uint8(v_e_1567_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1567_);
v___x_1578_ = lean_expr_instantiate_rev(v_binderType_1575_, v_fvars_1566_);
lean_dec_ref(v_binderType_1575_);
lean_inc_ref(v_post_1562_);
lean_inc_ref(v_pre_1561_);
v___x_1579_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1561_, v_post_1562_, v_usedLetOnly_1563_, v_skipConstInApp_1564_, v_skipInstances_1565_, v___x_1578_, v_a_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___f_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref(v___x_1579_);
v___x_1581_ = lean_box(v_usedLetOnly_1563_);
v___x_1582_ = lean_box(v_skipConstInApp_1564_);
v___x_1583_ = lean_box(v_skipInstances_1565_);
v___f_1584_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1584_, 0, v_fvars_1566_);
lean_closure_set(v___f_1584_, 1, v_pre_1561_);
lean_closure_set(v___f_1584_, 2, v_post_1562_);
lean_closure_set(v___f_1584_, 3, v___x_1581_);
lean_closure_set(v___f_1584_, 4, v___x_1582_);
lean_closure_set(v___f_1584_, 5, v___x_1583_);
lean_closure_set(v___f_1584_, 6, v_body_1576_);
v___x_1585_ = 0;
v___x_1586_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1574_, v_binderInfo_1577_, v_a_1580_, v___f_1584_, v___x_1585_, v_a_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
return v___x_1586_;
}
else
{
lean_dec_ref(v_body_1576_);
lean_dec(v_binderName_1574_);
lean_dec_ref(v_fvars_1566_);
lean_dec_ref(v_post_1562_);
lean_dec_ref(v_pre_1561_);
return v___x_1579_;
}
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_expr_instantiate_rev(v_e_1567_, v_fvars_1566_);
lean_dec_ref(v_e_1567_);
lean_inc_ref(v_post_1562_);
lean_inc_ref(v_pre_1561_);
v___x_1588_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1561_, v_post_1562_, v_usedLetOnly_1563_, v_skipConstInApp_1564_, v_skipInstances_1565_, v___x_1587_, v_a_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; uint8_t v___x_1590_; uint8_t v___x_1591_; uint8_t v___x_1592_; lean_object* v___x_1593_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = 0;
v___x_1591_ = 1;
v___x_1592_ = 1;
v___x_1593_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1566_, v_a_1589_, v___x_1590_, v_usedLetOnly_1563_, v___x_1590_, v___x_1591_, v___x_1592_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec_ref(v_fvars_1566_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1595_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref(v___x_1593_);
v___x_1595_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1561_, v_post_1562_, v_usedLetOnly_1563_, v_skipConstInApp_1564_, v_skipInstances_1565_, v_a_1594_, v_a_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
return v___x_1595_;
}
else
{
lean_dec_ref(v_post_1562_);
lean_dec_ref(v_pre_1561_);
return v___x_1593_;
}
}
else
{
lean_dec_ref(v_fvars_1566_);
lean_dec_ref(v_post_1562_);
lean_dec_ref(v_pre_1561_);
return v___x_1588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1596_, lean_object* v_pre_1597_, lean_object* v_post_1598_, uint8_t v_usedLetOnly_1599_, uint8_t v_skipConstInApp_1600_, uint8_t v_skipInstances_1601_, lean_object* v_body_1602_, lean_object* v_x_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_array_push(v_fvars_1596_, v_x_1603_);
v___x_1611_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1597_, v_post_1598_, v_usedLetOnly_1599_, v_skipConstInApp_1600_, v_skipInstances_1601_, v___x_1610_, v_body_1602_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1612_, lean_object* v_pre_1613_, lean_object* v_post_1614_, lean_object* v_usedLetOnly_1615_, lean_object* v_skipConstInApp_1616_, lean_object* v_skipInstances_1617_, lean_object* v_body_1618_, lean_object* v_x_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
uint8_t v_usedLetOnly_boxed_1626_; uint8_t v_skipConstInApp_boxed_1627_; uint8_t v_skipInstances_boxed_1628_; lean_object* v_res_1629_; 
v_usedLetOnly_boxed_1626_ = lean_unbox(v_usedLetOnly_1615_);
v_skipConstInApp_boxed_1627_ = lean_unbox(v_skipConstInApp_1616_);
v_skipInstances_boxed_1628_ = lean_unbox(v_skipInstances_1617_);
v_res_1629_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1612_, v_pre_1613_, v_post_1614_, v_usedLetOnly_boxed_1626_, v_skipConstInApp_boxed_1627_, v_skipInstances_boxed_1628_, v_body_1618_, v_x_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1630_, lean_object* v_post_1631_, uint8_t v_usedLetOnly_1632_, uint8_t v_skipConstInApp_1633_, uint8_t v_skipInstances_1634_, lean_object* v_fvars_1635_, lean_object* v_e_1636_, lean_object* v_a_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
if (lean_obj_tag(v_e_1636_) == 8)
{
lean_object* v_declName_1643_; lean_object* v_type_1644_; lean_object* v_value_1645_; lean_object* v_body_1646_; uint8_t v_nondep_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v_declName_1643_ = lean_ctor_get(v_e_1636_, 0);
lean_inc(v_declName_1643_);
v_type_1644_ = lean_ctor_get(v_e_1636_, 1);
lean_inc_ref(v_type_1644_);
v_value_1645_ = lean_ctor_get(v_e_1636_, 2);
lean_inc_ref(v_value_1645_);
v_body_1646_ = lean_ctor_get(v_e_1636_, 3);
lean_inc_ref(v_body_1646_);
v_nondep_1647_ = lean_ctor_get_uint8(v_e_1636_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1636_);
v___x_1648_ = lean_expr_instantiate_rev(v_type_1644_, v_fvars_1635_);
lean_dec_ref(v_type_1644_);
lean_inc_ref(v_post_1631_);
lean_inc_ref(v_pre_1630_);
v___x_1649_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1630_, v_post_1631_, v_usedLetOnly_1632_, v_skipConstInApp_1633_, v_skipInstances_1634_, v___x_1648_, v_a_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = lean_expr_instantiate_rev(v_value_1645_, v_fvars_1635_);
lean_dec_ref(v_value_1645_);
lean_inc_ref(v_post_1631_);
lean_inc_ref(v_pre_1630_);
v___x_1652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1630_, v_post_1631_, v_usedLetOnly_1632_, v_skipConstInApp_1633_, v_skipInstances_1634_, v___x_1651_, v_a_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___f_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = lean_box(v_usedLetOnly_1632_);
v___x_1655_ = lean_box(v_skipConstInApp_1633_);
v___x_1656_ = lean_box(v_skipInstances_1634_);
v___f_1657_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1657_, 0, v_fvars_1635_);
lean_closure_set(v___f_1657_, 1, v_pre_1630_);
lean_closure_set(v___f_1657_, 2, v_post_1631_);
lean_closure_set(v___f_1657_, 3, v___x_1654_);
lean_closure_set(v___f_1657_, 4, v___x_1655_);
lean_closure_set(v___f_1657_, 5, v___x_1656_);
lean_closure_set(v___f_1657_, 6, v_body_1646_);
v___x_1658_ = 0;
v___x_1659_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1643_, v_a_1650_, v_a_1653_, v___f_1657_, v_nondep_1647_, v___x_1658_, v_a_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
return v___x_1659_;
}
else
{
lean_dec(v_a_1650_);
lean_dec_ref(v_body_1646_);
lean_dec(v_declName_1643_);
lean_dec_ref(v_fvars_1635_);
lean_dec_ref(v_post_1631_);
lean_dec_ref(v_pre_1630_);
return v___x_1652_;
}
}
else
{
lean_dec_ref(v_body_1646_);
lean_dec_ref(v_value_1645_);
lean_dec(v_declName_1643_);
lean_dec_ref(v_fvars_1635_);
lean_dec_ref(v_post_1631_);
lean_dec_ref(v_pre_1630_);
return v___x_1649_;
}
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_expr_instantiate_rev(v_e_1636_, v_fvars_1635_);
lean_dec_ref(v_e_1636_);
lean_inc_ref(v_post_1631_);
lean_inc_ref(v_pre_1630_);
v___x_1661_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1630_, v_post_1631_, v_usedLetOnly_1632_, v_skipConstInApp_1633_, v_skipInstances_1634_, v___x_1660_, v_a_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; uint8_t v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref(v___x_1661_);
v___x_1663_ = 0;
v___x_1664_ = 1;
v___x_1665_ = l_Lean_Meta_mkLetFVars(v_fvars_1635_, v_a_1662_, v_usedLetOnly_1632_, v___x_1663_, v___x_1664_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec_ref(v_fvars_1635_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref(v___x_1665_);
v___x_1667_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1630_, v_post_1631_, v_usedLetOnly_1632_, v_skipConstInApp_1633_, v_skipInstances_1634_, v_a_1666_, v_a_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
return v___x_1667_;
}
else
{
lean_dec_ref(v_post_1631_);
lean_dec_ref(v_pre_1630_);
return v___x_1665_;
}
}
else
{
lean_dec_ref(v_fvars_1635_);
lean_dec_ref(v_post_1631_);
lean_dec_ref(v_pre_1630_);
return v___x_1661_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1668_; lean_object* v_dummy_1669_; 
v___x_1668_ = lean_box(0);
v_dummy_1669_ = l_Lean_Expr_sort___override(v___x_1668_);
return v_dummy_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1670_, lean_object* v_post_1671_, uint8_t v_usedLetOnly_1672_, uint8_t v_skipConstInApp_1673_, uint8_t v_skipInstances_1674_, size_t v_sz_1675_, size_t v_i_1676_, lean_object* v_bs_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_usize_dec_lt(v_i_1676_, v_sz_1675_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
lean_dec_ref(v_post_1671_);
lean_dec_ref(v_pre_1670_);
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_bs_1677_);
return v___x_1685_;
}
else
{
lean_object* v_v_1686_; lean_object* v___x_1687_; 
v_v_1686_ = lean_array_uget_borrowed(v_bs_1677_, v_i_1676_);
lean_inc(v_v_1686_);
lean_inc_ref(v_post_1671_);
lean_inc_ref(v_pre_1670_);
v___x_1687_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1670_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v_v_1686_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; lean_object* v_bs_x27_1690_; size_t v___x_1691_; size_t v___x_1692_; lean_object* v___x_1693_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref(v___x_1687_);
v___x_1689_ = lean_unsigned_to_nat(0u);
v_bs_x27_1690_ = lean_array_uset(v_bs_1677_, v_i_1676_, v___x_1689_);
v___x_1691_ = ((size_t)1ULL);
v___x_1692_ = lean_usize_add(v_i_1676_, v___x_1691_);
v___x_1693_ = lean_array_uset(v_bs_x27_1690_, v_i_1676_, v_a_1688_);
v_i_1676_ = v___x_1692_;
v_bs_1677_ = v___x_1693_;
goto _start;
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec_ref(v_bs_1677_);
lean_dec_ref(v_post_1671_);
lean_dec_ref(v_pre_1670_);
v_a_1695_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1687_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1687_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1703_, lean_object* v_post_1704_, uint8_t v_usedLetOnly_1705_, uint8_t v_skipConstInApp_1706_, uint8_t v_skipInstances_1707_, lean_object* v___x_1708_, lean_object* v___y_1709_, lean_object* v_b_1710_, lean_object* v_a_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1703_, v_post_1704_, v_usedLetOnly_1705_, v_skipConstInApp_1706_, v_skipInstances_1707_, v___x_1708_, v___y_1709_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1727_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1722_ = lean_array_fset(v_b_1710_, v_a_1711_, v_a_1718_);
v___x_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1723_);
v___x_1725_ = v___x_1720_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec_ref(v_b_1710_);
v_a_1728_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1717_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1717_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1736_, lean_object* v_post_1737_, lean_object* v_usedLetOnly_1738_, lean_object* v_skipConstInApp_1739_, lean_object* v_skipInstances_1740_, lean_object* v___x_1741_, lean_object* v___y_1742_, lean_object* v_b_1743_, lean_object* v_a_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
uint8_t v_usedLetOnly_boxed_1750_; uint8_t v_skipConstInApp_boxed_1751_; uint8_t v_skipInstances_boxed_1752_; lean_object* v_res_1753_; 
v_usedLetOnly_boxed_1750_ = lean_unbox(v_usedLetOnly_1738_);
v_skipConstInApp_boxed_1751_ = lean_unbox(v_skipConstInApp_1739_);
v_skipInstances_boxed_1752_ = lean_unbox(v_skipInstances_1740_);
v_res_1753_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1736_, v_post_1737_, v_usedLetOnly_boxed_1750_, v_skipConstInApp_boxed_1751_, v_skipInstances_boxed_1752_, v___x_1741_, v___y_1742_, v_b_1743_, v_a_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v_a_1744_);
lean_dec(v___y_1742_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1754_, lean_object* v___x_1755_, lean_object* v_pre_1756_, lean_object* v_post_1757_, uint8_t v_usedLetOnly_1758_, uint8_t v_skipConstInApp_1759_, uint8_t v_skipInstances_1760_, lean_object* v_a_1761_, lean_object* v_b_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___y_1770_; uint8_t v___x_1793_; 
v___x_1793_ = lean_nat_dec_lt(v_a_1761_, v_upperBound_1754_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; 
lean_dec(v_a_1761_);
lean_dec_ref(v_post_1757_);
lean_dec_ref(v_pre_1756_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_b_1762_);
return v___x_1794_;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1795_ = lean_array_fget_borrowed(v_b_1762_, v_a_1761_);
v___x_1796_ = lean_array_get_size(v___x_1755_);
v___x_1797_ = lean_nat_dec_lt(v_a_1761_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___f_1801_; 
lean_inc(v___x_1795_);
v___x_1798_ = lean_box(v_usedLetOnly_1758_);
v___x_1799_ = lean_box(v_skipConstInApp_1759_);
v___x_1800_ = lean_box(v_skipInstances_1760_);
lean_inc(v_a_1761_);
lean_inc(v___y_1763_);
lean_inc_ref(v_post_1757_);
lean_inc_ref(v_pre_1756_);
v___f_1801_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1801_, 0, v_pre_1756_);
lean_closure_set(v___f_1801_, 1, v_post_1757_);
lean_closure_set(v___f_1801_, 2, v___x_1798_);
lean_closure_set(v___f_1801_, 3, v___x_1799_);
lean_closure_set(v___f_1801_, 4, v___x_1800_);
lean_closure_set(v___f_1801_, 5, v___x_1795_);
lean_closure_set(v___f_1801_, 6, v___y_1763_);
lean_closure_set(v___f_1801_, 7, v_b_1762_);
lean_closure_set(v___f_1801_, 8, v_a_1761_);
v___y_1770_ = v___f_1801_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1802_; uint8_t v_isInstance_1803_; 
v___x_1802_ = lean_array_fget_borrowed(v___x_1755_, v_a_1761_);
v_isInstance_1803_ = lean_ctor_get_uint8(v___x_1802_, sizeof(void*)*1 + 4);
if (v_isInstance_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___f_1807_; 
lean_inc(v___x_1795_);
v___x_1804_ = lean_box(v_usedLetOnly_1758_);
v___x_1805_ = lean_box(v_skipConstInApp_1759_);
v___x_1806_ = lean_box(v_skipInstances_1760_);
lean_inc(v_a_1761_);
lean_inc(v___y_1763_);
lean_inc_ref(v_post_1757_);
lean_inc_ref(v_pre_1756_);
v___f_1807_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1807_, 0, v_pre_1756_);
lean_closure_set(v___f_1807_, 1, v_post_1757_);
lean_closure_set(v___f_1807_, 2, v___x_1804_);
lean_closure_set(v___f_1807_, 3, v___x_1805_);
lean_closure_set(v___f_1807_, 4, v___x_1806_);
lean_closure_set(v___f_1807_, 5, v___x_1795_);
lean_closure_set(v___f_1807_, 6, v___y_1763_);
lean_closure_set(v___f_1807_, 7, v_b_1762_);
lean_closure_set(v___f_1807_, 8, v_a_1761_);
v___y_1770_ = v___f_1807_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1808_; lean_object* v___f_1809_; 
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v_b_1762_);
v___f_1809_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1809_, 0, v___x_1808_);
v___y_1770_ = v___f_1809_;
goto v___jp_1769_;
}
}
}
v___jp_1769_:
{
lean_object* v___x_1771_; 
lean_inc(v___y_1767_);
lean_inc_ref(v___y_1766_);
lean_inc(v___y_1765_);
lean_inc_ref(v___y_1764_);
v___x_1771_ = lean_apply_5(v___y_1770_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, lean_box(0));
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1784_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1784_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1784_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
if (lean_obj_tag(v_a_1772_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; 
lean_dec(v_a_1761_);
lean_dec_ref(v_post_1757_);
lean_dec_ref(v_pre_1756_);
v_a_1776_ = lean_ctor_get(v_a_1772_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v_a_1772_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v_a_1776_);
v___x_1778_ = v___x_1774_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_del_object(v___x_1774_);
v_a_1780_ = lean_ctor_get(v_a_1772_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v_a_1772_);
v___x_1781_ = lean_unsigned_to_nat(1u);
v___x_1782_ = lean_nat_add(v_a_1761_, v___x_1781_);
lean_dec(v_a_1761_);
v_a_1761_ = v___x_1782_;
v_b_1762_ = v_a_1780_;
goto _start;
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_a_1761_);
lean_dec_ref(v_post_1757_);
lean_dec_ref(v_pre_1756_);
v_a_1785_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1771_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1771_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1810_, lean_object* v_pre_1811_, lean_object* v_post_1812_, uint8_t v_usedLetOnly_1813_, uint8_t v_skipConstInApp_1814_, lean_object* v_x_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_f_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; 
if (lean_obj_tag(v_x_1815_) == 5)
{
lean_object* v_fn_1873_; lean_object* v_arg_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_fn_1873_ = lean_ctor_get(v_x_1815_, 0);
lean_inc_ref(v_fn_1873_);
v_arg_1874_ = lean_ctor_get(v_x_1815_, 1);
lean_inc_ref(v_arg_1874_);
lean_dec_ref(v_x_1815_);
v___x_1875_ = lean_array_set(v_x_1816_, v_x_1817_, v_arg_1874_);
v___x_1876_ = lean_unsigned_to_nat(1u);
v___x_1877_ = lean_nat_sub(v_x_1817_, v___x_1876_);
lean_dec(v_x_1817_);
v_x_1815_ = v_fn_1873_;
v_x_1816_ = v___x_1875_;
v_x_1817_ = v___x_1877_;
goto _start;
}
else
{
lean_dec(v_x_1817_);
if (v_skipConstInApp_1814_ == 0)
{
goto v___jp_1870_;
}
else
{
uint8_t v___x_1879_; 
v___x_1879_ = l_Lean_Expr_isConst(v_x_1815_);
if (v___x_1879_ == 0)
{
goto v___jp_1870_;
}
else
{
v_f_1825_ = v_x_1815_;
v___y_1826_ = v___y_1818_;
v___y_1827_ = v___y_1819_;
v___y_1828_ = v___y_1820_;
v___y_1829_ = v___y_1821_;
v___y_1830_ = v___y_1822_;
goto v___jp_1824_;
}
}
}
v___jp_1824_:
{
if (v_skipInstances_1810_ == 0)
{
size_t v_sz_1831_; size_t v___x_1832_; lean_object* v___x_1833_; 
v_sz_1831_ = lean_array_size(v_x_1816_);
v___x_1832_ = ((size_t)0ULL);
lean_inc_ref(v_post_1812_);
lean_inc_ref(v_pre_1811_);
v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1811_, v_post_1812_, v_usedLetOnly_1813_, v_skipConstInApp_1814_, v_skipInstances_1810_, v_sz_1831_, v___x_1832_, v_x_1816_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref(v___x_1833_);
v___x_1835_ = l_Lean_mkAppN(v_f_1825_, v_a_1834_);
lean_dec(v_a_1834_);
v___x_1836_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1811_, v_post_1812_, v_usedLetOnly_1813_, v_skipConstInApp_1814_, v_skipInstances_1810_, v___x_1835_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
return v___x_1836_;
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec_ref(v_f_1825_);
lean_dec_ref(v_post_1812_);
lean_dec_ref(v_pre_1811_);
v_a_1837_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1833_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1833_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_array_get_size(v_x_1816_);
lean_inc_ref(v_f_1825_);
v___x_1846_ = l_Lean_Meta_getFunInfoNArgs(v_f_1825_, v___x_1845_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v_paramInfo_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1846_);
v_paramInfo_1848_ = lean_ctor_get(v_a_1847_, 0);
lean_inc_ref(v_paramInfo_1848_);
lean_dec(v_a_1847_);
v___x_1849_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1812_);
lean_inc_ref(v_pre_1811_);
v___x_1850_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1845_, v_paramInfo_1848_, v_pre_1811_, v_post_1812_, v_usedLetOnly_1813_, v_skipConstInApp_1814_, v_skipInstances_1810_, v___x_1849_, v_x_1816_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec_ref(v_paramInfo_1848_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref(v___x_1850_);
v___x_1852_ = l_Lean_mkAppN(v_f_1825_, v_a_1851_);
lean_dec(v_a_1851_);
v___x_1853_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1811_, v_post_1812_, v_usedLetOnly_1813_, v_skipConstInApp_1814_, v_skipInstances_1810_, v___x_1852_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
return v___x_1853_;
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v_f_1825_);
lean_dec_ref(v_post_1812_);
lean_dec_ref(v_pre_1811_);
v_a_1854_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1850_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1850_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v_f_1825_);
lean_dec_ref(v_x_1816_);
lean_dec_ref(v_post_1812_);
lean_dec_ref(v_pre_1811_);
v_a_1862_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1846_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1846_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
v___jp_1870_:
{
lean_object* v___x_1871_; 
lean_inc_ref(v_post_1812_);
lean_inc_ref(v_pre_1811_);
v___x_1871_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1811_, v_post_1812_, v_usedLetOnly_1813_, v_skipConstInApp_1814_, v_skipInstances_1810_, v_x_1815_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref(v___x_1871_);
v_f_1825_ = v_a_1872_;
v___y_1826_ = v___y_1818_;
v___y_1827_ = v___y_1819_;
v___y_1828_ = v___y_1820_;
v___y_1829_ = v___y_1821_;
v___y_1830_ = v___y_1822_;
goto v___jp_1824_;
}
else
{
lean_dec_ref(v_x_1816_);
lean_dec_ref(v_post_1812_);
lean_dec_ref(v_pre_1811_);
return v___x_1871_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v_pre_1880_, lean_object* v_e_1881_, lean_object* v_post_1882_, uint8_t v_usedLetOnly_1883_, uint8_t v_skipConstInApp_1884_, uint8_t v_skipInstances_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; 
lean_inc_ref(v_pre_1880_);
lean_inc(v___y_1890_);
lean_inc_ref(v___y_1889_);
lean_inc(v___y_1888_);
lean_inc_ref(v___y_1887_);
lean_inc_ref(v_e_1881_);
v___x_1892_ = lean_apply_6(v_pre_1880_, v_e_1881_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, lean_box(0));
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1941_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1941_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1941_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___y_1898_; 
switch(lean_obj_tag(v_a_1893_))
{
case 0:
{
lean_object* v_e_1933_; lean_object* v___x_1935_; 
lean_dec_ref(v_post_1882_);
lean_dec_ref(v_e_1881_);
lean_dec_ref(v_pre_1880_);
v_e_1933_ = lean_ctor_get(v_a_1893_, 0);
lean_inc_ref(v_e_1933_);
lean_dec_ref(v_a_1893_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v_e_1933_);
v___x_1935_ = v___x_1895_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_e_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
case 1:
{
lean_object* v_e_1937_; lean_object* v___x_1938_; 
lean_del_object(v___x_1895_);
lean_dec_ref(v_e_1881_);
v_e_1937_ = lean_ctor_get(v_a_1893_, 0);
lean_inc_ref(v_e_1937_);
lean_dec_ref(v_a_1893_);
v___x_1938_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1880_, v_post_1882_, v_usedLetOnly_1883_, v_skipConstInApp_1884_, v_skipInstances_1885_, v_e_1937_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1938_;
}
default: 
{
lean_object* v_e_x3f_1939_; 
lean_del_object(v___x_1895_);
v_e_x3f_1939_ = lean_ctor_get(v_a_1893_, 0);
lean_inc(v_e_x3f_1939_);
lean_dec_ref(v_a_1893_);
if (lean_obj_tag(v_e_x3f_1939_) == 0)
{
v___y_1898_ = v_e_1881_;
goto v___jp_1897_;
}
else
{
lean_object* v_val_1940_; 
lean_dec_ref(v_e_1881_);
v_val_1940_ = lean_ctor_get(v_e_x3f_1939_, 0);
lean_inc(v_val_1940_);
lean_dec_ref(v_e_x3f_1939_);
v___y_1898_ = v_val_1940_;
goto v___jp_1897_;
}
}
}
v___jp_1897_:
{
switch(lean_obj_tag(v___y_1898_))
{
case 7:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1900_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1880_, v_post_1882_, v_usedLetOnly_1883_, v_skipConstInApp_1884_, v_skipInstances_1885_, v___x_1899_, v___y_1898_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1900_;
}
case 6:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1902_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1880_, v_post_1882_, v_usedLetOnly_1883_, v_skipConstInApp_1884_, v_skipInstances_1885_, v___x_1901_, v___y_1898_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1902_;
}
case 8:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1904_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1880_, v_post_1882_, v_usedLetOnly_1883_, v_skipConstInApp_1884_, v_skipInstances_1885_, v___x_1903_, v___y_1898_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1904_;
}
case 5:
{
lean_object* v_dummy_1905_; lean_object* v_nargs_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_dummy_1905_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_1906_ = l_Lean_Expr_getAppNumArgs(v___y_1898_);
lean_inc(v_nargs_1906_);
v___x_1907_ = lean_mk_array(v_nargs_1906_, v_dummy_1905_);
v___x_1908_ = lean_unsigned_to_nat(1u);
v___x_1909_ = lean_nat_sub(v_nargs_1906_, v___x_1908_);
lean_dec(v_nargs_1906_);
v___x_1910_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1885_, v_pre_1880_, v_post_1882_, v_usedLetOnly_1883_, v_skipConstInApp_1884_, v___y_1898_, v___x_1907_, v___x_1909_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1910_;
}
case 10:
{
lean_object* v_data_1911_; lean_object* v_expr_1912_; lean_object* v___x_1913_; 
v_data_1911_ = lean_ctor_get(v___y_1898_, 0);
v_expr_1912_ = lean_ctor_get(v___y_1898_, 1);
lean_inc_ref(v_expr_1912_);
lean_inc_ref(v_post_1882_);
lean_inc_ref(v_pre_1880_);
v___x_1913_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1880_, v_post_1882_, v_usedLetOnly_1883_, v_skipConstInApp_1884_, v_skipInstances_1885_, v_expr_1912_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; size_t v___x_1915_; size_t v___x_1916_; uint8_t v___x_1917_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref(v___x_1913_);
v___x_1915_ = lean_ptr_addr(v_expr_1912_);
v___x_1916_ = lean_ptr_addr(v_a_1914_);
v___x_1917_ = lean_usize_dec_eq(v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_inc(v_data_1911_);
lean_dec_ref(v___y_1898_);
v___x_1918_ = l_Lean_Expr_mdata___override(v_data_1911_, v_a_1914_);
v___x_1919_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1880_, v_post_1882_, v_usedLetOnly_1883_, v_skipConstInApp_1884_, v_skipInstances_1885_, v___x_1918_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; 
lean_dec(v_a_1914_);
v___x_1920_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1880_, v_post_1882_, v_usedLetOnly_1883_, v_skipConstInApp_1884_, v_skipInstances_1885_, v___y_1898_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1920_;
}
}
else
{
lean_dec_ref(v___y_1898_);
lean_dec_ref(v_post_1882_);
lean_dec_ref(v_pre_1880_);
return v___x_1913_;
}
}
case 11:
{
lean_object* v_typeName_1921_; lean_object* v_idx_1922_; lean_object* v_struct_1923_; lean_object* v___x_1924_; 
v_typeName_1921_ = lean_ctor_get(v___y_1898_, 0);
v_idx_1922_ = lean_ctor_get(v___y_1898_, 1);
v_struct_1923_ = lean_ctor_get(v___y_1898_, 2);
lean_inc_ref(v_struct_1923_);
lean_inc_ref(v_post_1882_);
lean_inc_ref(v_pre_1880_);
v___x_1924_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1880_, v_post_1882_, v_usedLetOnly_1883_, v_skipConstInApp_1884_, v_skipInstances_1885_, v_struct_1923_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; size_t v___x_1926_; size_t v___x_1927_; uint8_t v___x_1928_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1924_);
v___x_1926_ = lean_ptr_addr(v_struct_1923_);
v___x_1927_ = lean_ptr_addr(v_a_1925_);
v___x_1928_ = lean_usize_dec_eq(v___x_1926_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_inc(v_idx_1922_);
lean_inc(v_typeName_1921_);
lean_dec_ref(v___y_1898_);
v___x_1929_ = l_Lean_Expr_proj___override(v_typeName_1921_, v_idx_1922_, v_a_1925_);
v___x_1930_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1880_, v_post_1882_, v_usedLetOnly_1883_, v_skipConstInApp_1884_, v_skipInstances_1885_, v___x_1929_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1930_;
}
else
{
lean_object* v___x_1931_; 
lean_dec(v_a_1925_);
v___x_1931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1880_, v_post_1882_, v_usedLetOnly_1883_, v_skipConstInApp_1884_, v_skipInstances_1885_, v___y_1898_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1931_;
}
}
else
{
lean_dec_ref(v___y_1898_);
lean_dec_ref(v_post_1882_);
lean_dec_ref(v_pre_1880_);
return v___x_1924_;
}
}
default: 
{
lean_object* v___x_1932_; 
v___x_1932_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1880_, v_post_1882_, v_usedLetOnly_1883_, v_skipConstInApp_1884_, v_skipInstances_1885_, v___y_1898_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1932_;
}
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref(v_post_1882_);
lean_dec_ref(v_e_1881_);
lean_dec_ref(v_pre_1880_);
v_a_1942_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1892_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1892_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v_pre_1950_, lean_object* v_e_1951_, lean_object* v_post_1952_, lean_object* v_usedLetOnly_1953_, lean_object* v_skipConstInApp_1954_, lean_object* v_skipInstances_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
uint8_t v_usedLetOnly_boxed_1962_; uint8_t v_skipConstInApp_boxed_1963_; uint8_t v_skipInstances_boxed_1964_; lean_object* v_res_1965_; 
v_usedLetOnly_boxed_1962_ = lean_unbox(v_usedLetOnly_1953_);
v_skipConstInApp_boxed_1963_ = lean_unbox(v_skipConstInApp_1954_);
v_skipInstances_boxed_1964_ = lean_unbox(v_skipInstances_1955_);
v_res_1965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v_pre_1950_, v_e_1951_, v_post_1952_, v_usedLetOnly_boxed_1962_, v_skipConstInApp_boxed_1963_, v_skipInstances_boxed_1964_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_1966_, lean_object* v_post_1967_, uint8_t v_usedLetOnly_1968_, uint8_t v_skipConstInApp_1969_, uint8_t v_skipInstances_1970_, lean_object* v_e_1971_, lean_object* v_a_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_inc(v_a_1972_);
v___x_1978_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1978_, 0, lean_box(0));
lean_closure_set(v___x_1978_, 1, lean_box(0));
lean_closure_set(v___x_1978_, 2, v_a_1972_);
v___x_1979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_1978_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2013_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_2013_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2013_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_1980_, v_e_1971_);
lean_dec(v_a_1980_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; 
lean_del_object(v___x_1982_);
v___x_1985_ = lean_box(v_usedLetOnly_1968_);
v___x_1986_ = lean_box(v_skipConstInApp_1969_);
v___x_1987_ = lean_box(v_skipInstances_1970_);
lean_inc_ref(v_e_1971_);
v___f_1988_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1988_, 0, v_pre_1966_);
lean_closure_set(v___f_1988_, 1, v_e_1971_);
lean_closure_set(v___f_1988_, 2, v_post_1967_);
lean_closure_set(v___f_1988_, 3, v___x_1985_);
lean_closure_set(v___f_1988_, 4, v___x_1986_);
lean_closure_set(v___f_1988_, 5, v___x_1987_);
lean_inc_ref(v___y_1975_);
v___x_1989_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_1988_, v_a_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___f_1991_; lean_object* v___x_1992_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref(v___x_1989_);
lean_inc(v_a_1990_);
lean_inc(v_a_1972_);
v___f_1991_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1991_, 0, v_a_1972_);
lean_closure_set(v___f_1991_, 1, v_e_1971_);
lean_closure_set(v___f_1991_, 2, v_a_1990_);
v___x_1992_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_1991_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; 
v_unused_2000_ = lean_ctor_get(v___x_1992_, 0);
lean_dec(v_unused_2000_);
v___x_1994_ = v___x_1992_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_dec(v___x_1992_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v_a_1990_);
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1990_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_a_1990_);
v_a_2001_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1992_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1992_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_dec_ref(v_e_1971_);
return v___x_1989_;
}
}
else
{
lean_object* v_val_2009_; lean_object* v___x_2011_; 
lean_dec_ref(v_e_1971_);
lean_dec_ref(v_post_1967_);
lean_dec_ref(v_pre_1966_);
v_val_2009_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_val_2009_);
lean_dec_ref(v___x_1984_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v_val_2009_);
v___x_2011_ = v___x_1982_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_val_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec_ref(v_e_1971_);
lean_dec_ref(v_post_1967_);
lean_dec_ref(v_pre_1966_);
v_a_2014_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_1979_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_1979_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_2022_, lean_object* v_pre_2023_, lean_object* v_post_2024_, lean_object* v_usedLetOnly_2025_, lean_object* v_skipConstInApp_2026_, lean_object* v_skipInstances_2027_, lean_object* v_body_2028_, lean_object* v_x_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
uint8_t v_usedLetOnly_boxed_2036_; uint8_t v_skipConstInApp_boxed_2037_; uint8_t v_skipInstances_boxed_2038_; lean_object* v_res_2039_; 
v_usedLetOnly_boxed_2036_ = lean_unbox(v_usedLetOnly_2025_);
v_skipConstInApp_boxed_2037_ = lean_unbox(v_skipConstInApp_2026_);
v_skipInstances_boxed_2038_ = lean_unbox(v_skipInstances_2027_);
v_res_2039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_2022_, v_pre_2023_, v_post_2024_, v_usedLetOnly_boxed_2036_, v_skipConstInApp_boxed_2037_, v_skipInstances_boxed_2038_, v_body_2028_, v_x_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2040_, lean_object* v_post_2041_, uint8_t v_usedLetOnly_2042_, uint8_t v_skipConstInApp_2043_, uint8_t v_skipInstances_2044_, lean_object* v_fvars_2045_, lean_object* v_e_2046_, lean_object* v_a_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
if (lean_obj_tag(v_e_2046_) == 7)
{
lean_object* v_binderName_2053_; lean_object* v_binderType_2054_; lean_object* v_body_2055_; uint8_t v_binderInfo_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_binderName_2053_ = lean_ctor_get(v_e_2046_, 0);
lean_inc(v_binderName_2053_);
v_binderType_2054_ = lean_ctor_get(v_e_2046_, 1);
lean_inc_ref(v_binderType_2054_);
v_body_2055_ = lean_ctor_get(v_e_2046_, 2);
lean_inc_ref(v_body_2055_);
v_binderInfo_2056_ = lean_ctor_get_uint8(v_e_2046_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2046_);
v___x_2057_ = lean_expr_instantiate_rev(v_binderType_2054_, v_fvars_2045_);
lean_dec_ref(v_binderType_2054_);
lean_inc_ref(v_post_2041_);
lean_inc_ref(v_pre_2040_);
v___x_2058_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2040_, v_post_2041_, v_usedLetOnly_2042_, v_skipConstInApp_2043_, v_skipInstances_2044_, v___x_2057_, v_a_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___f_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref(v___x_2058_);
v___x_2060_ = lean_box(v_usedLetOnly_2042_);
v___x_2061_ = lean_box(v_skipConstInApp_2043_);
v___x_2062_ = lean_box(v_skipInstances_2044_);
v___f_2063_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2063_, 0, v_fvars_2045_);
lean_closure_set(v___f_2063_, 1, v_pre_2040_);
lean_closure_set(v___f_2063_, 2, v_post_2041_);
lean_closure_set(v___f_2063_, 3, v___x_2060_);
lean_closure_set(v___f_2063_, 4, v___x_2061_);
lean_closure_set(v___f_2063_, 5, v___x_2062_);
lean_closure_set(v___f_2063_, 6, v_body_2055_);
v___x_2064_ = 0;
v___x_2065_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2053_, v_binderInfo_2056_, v_a_2059_, v___f_2063_, v___x_2064_, v_a_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
return v___x_2065_;
}
else
{
lean_dec_ref(v_body_2055_);
lean_dec(v_binderName_2053_);
lean_dec_ref(v_fvars_2045_);
lean_dec_ref(v_post_2041_);
lean_dec_ref(v_pre_2040_);
return v___x_2058_;
}
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = lean_expr_instantiate_rev(v_e_2046_, v_fvars_2045_);
lean_dec_ref(v_e_2046_);
lean_inc_ref(v_post_2041_);
lean_inc_ref(v_pre_2040_);
v___x_2067_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2040_, v_post_2041_, v_usedLetOnly_2042_, v_skipConstInApp_2043_, v_skipInstances_2044_, v___x_2066_, v_a_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; uint8_t v___x_2069_; uint8_t v___x_2070_; uint8_t v___x_2071_; lean_object* v___x_2072_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref(v___x_2067_);
v___x_2069_ = 0;
v___x_2070_ = 1;
v___x_2071_ = 1;
v___x_2072_ = l_Lean_Meta_mkForallFVars(v_fvars_2045_, v_a_2068_, v___x_2069_, v_usedLetOnly_2042_, v___x_2070_, v___x_2071_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec_ref(v_fvars_2045_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2074_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref(v___x_2072_);
v___x_2074_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2040_, v_post_2041_, v_usedLetOnly_2042_, v_skipConstInApp_2043_, v_skipInstances_2044_, v_a_2073_, v_a_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
return v___x_2074_;
}
else
{
lean_dec_ref(v_post_2041_);
lean_dec_ref(v_pre_2040_);
return v___x_2072_;
}
}
else
{
lean_dec_ref(v_fvars_2045_);
lean_dec_ref(v_post_2041_);
lean_dec_ref(v_pre_2040_);
return v___x_2067_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2075_, lean_object* v_pre_2076_, lean_object* v_post_2077_, uint8_t v_usedLetOnly_2078_, uint8_t v_skipConstInApp_2079_, uint8_t v_skipInstances_2080_, lean_object* v_body_2081_, lean_object* v_x_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_array_push(v_fvars_2075_, v_x_2082_);
v___x_2090_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2076_, v_post_2077_, v_usedLetOnly_2078_, v_skipConstInApp_2079_, v_skipInstances_2080_, v___x_2089_, v_body_2081_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2091_, lean_object* v_post_2092_, lean_object* v_usedLetOnly_2093_, lean_object* v_skipConstInApp_2094_, lean_object* v_skipInstances_2095_, lean_object* v_e_2096_, lean_object* v_a_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
uint8_t v_usedLetOnly_boxed_2103_; uint8_t v_skipConstInApp_boxed_2104_; uint8_t v_skipInstances_boxed_2105_; lean_object* v_res_2106_; 
v_usedLetOnly_boxed_2103_ = lean_unbox(v_usedLetOnly_2093_);
v_skipConstInApp_boxed_2104_ = lean_unbox(v_skipConstInApp_2094_);
v_skipInstances_boxed_2105_ = lean_unbox(v_skipInstances_2095_);
v_res_2106_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2091_, v_post_2092_, v_usedLetOnly_boxed_2103_, v_skipConstInApp_boxed_2104_, v_skipInstances_boxed_2105_, v_e_2096_, v_a_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v_a_2097_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_pre_2107_, lean_object* v_post_2108_, lean_object* v_usedLetOnly_2109_, lean_object* v_skipConstInApp_2110_, lean_object* v_skipInstances_2111_, lean_object* v_sz_2112_, lean_object* v_i_2113_, lean_object* v_bs_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
uint8_t v_usedLetOnly_boxed_2121_; uint8_t v_skipConstInApp_boxed_2122_; uint8_t v_skipInstances_boxed_2123_; size_t v_sz_boxed_2124_; size_t v_i_boxed_2125_; lean_object* v_res_2126_; 
v_usedLetOnly_boxed_2121_ = lean_unbox(v_usedLetOnly_2109_);
v_skipConstInApp_boxed_2122_ = lean_unbox(v_skipConstInApp_2110_);
v_skipInstances_boxed_2123_ = lean_unbox(v_skipInstances_2111_);
v_sz_boxed_2124_ = lean_unbox_usize(v_sz_2112_);
lean_dec(v_sz_2112_);
v_i_boxed_2125_ = lean_unbox_usize(v_i_2113_);
lean_dec(v_i_2113_);
v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_2107_, v_post_2108_, v_usedLetOnly_boxed_2121_, v_skipConstInApp_boxed_2122_, v_skipInstances_boxed_2123_, v_sz_boxed_2124_, v_i_boxed_2125_, v_bs_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2127_, lean_object* v_post_2128_, lean_object* v_usedLetOnly_2129_, lean_object* v_skipConstInApp_2130_, lean_object* v_skipInstances_2131_, lean_object* v_e_2132_, lean_object* v_a_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
uint8_t v_usedLetOnly_boxed_2139_; uint8_t v_skipConstInApp_boxed_2140_; uint8_t v_skipInstances_boxed_2141_; lean_object* v_res_2142_; 
v_usedLetOnly_boxed_2139_ = lean_unbox(v_usedLetOnly_2129_);
v_skipConstInApp_boxed_2140_ = lean_unbox(v_skipConstInApp_2130_);
v_skipInstances_boxed_2141_ = lean_unbox(v_skipInstances_2131_);
v_res_2142_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2127_, v_post_2128_, v_usedLetOnly_boxed_2139_, v_skipConstInApp_boxed_2140_, v_skipInstances_boxed_2141_, v_e_2132_, v_a_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v_a_2133_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2143_, lean_object* v_post_2144_, lean_object* v_usedLetOnly_2145_, lean_object* v_skipConstInApp_2146_, lean_object* v_skipInstances_2147_, lean_object* v_fvars_2148_, lean_object* v_e_2149_, lean_object* v_a_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
uint8_t v_usedLetOnly_boxed_2156_; uint8_t v_skipConstInApp_boxed_2157_; uint8_t v_skipInstances_boxed_2158_; lean_object* v_res_2159_; 
v_usedLetOnly_boxed_2156_ = lean_unbox(v_usedLetOnly_2145_);
v_skipConstInApp_boxed_2157_ = lean_unbox(v_skipConstInApp_2146_);
v_skipInstances_boxed_2158_ = lean_unbox(v_skipInstances_2147_);
v_res_2159_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2143_, v_post_2144_, v_usedLetOnly_boxed_2156_, v_skipConstInApp_boxed_2157_, v_skipInstances_boxed_2158_, v_fvars_2148_, v_e_2149_, v_a_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v_a_2150_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2160_, lean_object* v_post_2161_, lean_object* v_usedLetOnly_2162_, lean_object* v_skipConstInApp_2163_, lean_object* v_skipInstances_2164_, lean_object* v_fvars_2165_, lean_object* v_e_2166_, lean_object* v_a_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
uint8_t v_usedLetOnly_boxed_2173_; uint8_t v_skipConstInApp_boxed_2174_; uint8_t v_skipInstances_boxed_2175_; lean_object* v_res_2176_; 
v_usedLetOnly_boxed_2173_ = lean_unbox(v_usedLetOnly_2162_);
v_skipConstInApp_boxed_2174_ = lean_unbox(v_skipConstInApp_2163_);
v_skipInstances_boxed_2175_ = lean_unbox(v_skipInstances_2164_);
v_res_2176_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2160_, v_post_2161_, v_usedLetOnly_boxed_2173_, v_skipConstInApp_boxed_2174_, v_skipInstances_boxed_2175_, v_fvars_2165_, v_e_2166_, v_a_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v_a_2167_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2177_, lean_object* v_post_2178_, lean_object* v_usedLetOnly_2179_, lean_object* v_skipConstInApp_2180_, lean_object* v_skipInstances_2181_, lean_object* v_fvars_2182_, lean_object* v_e_2183_, lean_object* v_a_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
uint8_t v_usedLetOnly_boxed_2190_; uint8_t v_skipConstInApp_boxed_2191_; uint8_t v_skipInstances_boxed_2192_; lean_object* v_res_2193_; 
v_usedLetOnly_boxed_2190_ = lean_unbox(v_usedLetOnly_2179_);
v_skipConstInApp_boxed_2191_ = lean_unbox(v_skipConstInApp_2180_);
v_skipInstances_boxed_2192_ = lean_unbox(v_skipInstances_2181_);
v_res_2193_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2177_, v_post_2178_, v_usedLetOnly_boxed_2190_, v_skipConstInApp_boxed_2191_, v_skipInstances_boxed_2192_, v_fvars_2182_, v_e_2183_, v_a_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v_a_2184_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object* v_upperBound_2194_, lean_object* v___x_2195_, lean_object* v_pre_2196_, lean_object* v_post_2197_, lean_object* v_usedLetOnly_2198_, lean_object* v_skipConstInApp_2199_, lean_object* v_skipInstances_2200_, lean_object* v_a_2201_, lean_object* v_b_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
uint8_t v_usedLetOnly_boxed_2209_; uint8_t v_skipConstInApp_boxed_2210_; uint8_t v_skipInstances_boxed_2211_; lean_object* v_res_2212_; 
v_usedLetOnly_boxed_2209_ = lean_unbox(v_usedLetOnly_2198_);
v_skipConstInApp_boxed_2210_ = lean_unbox(v_skipConstInApp_2199_);
v_skipInstances_boxed_2211_ = lean_unbox(v_skipInstances_2200_);
v_res_2212_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_2194_, v___x_2195_, v_pre_2196_, v_post_2197_, v_usedLetOnly_boxed_2209_, v_skipConstInApp_boxed_2210_, v_skipInstances_boxed_2211_, v_a_2201_, v_b_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___x_2195_);
lean_dec(v_upperBound_2194_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2213_, lean_object* v_pre_2214_, lean_object* v_post_2215_, lean_object* v_usedLetOnly_2216_, lean_object* v_skipConstInApp_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_, lean_object* v_x_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v_skipInstances_boxed_2227_; uint8_t v_usedLetOnly_boxed_2228_; uint8_t v_skipConstInApp_boxed_2229_; lean_object* v_res_2230_; 
v_skipInstances_boxed_2227_ = lean_unbox(v_skipInstances_2213_);
v_usedLetOnly_boxed_2228_ = lean_unbox(v_usedLetOnly_2216_);
v_skipConstInApp_boxed_2229_ = lean_unbox(v_skipConstInApp_2217_);
v_res_2230_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2227_, v_pre_2214_, v_post_2215_, v_usedLetOnly_boxed_2228_, v_skipConstInApp_boxed_2229_, v_x_2218_, v_x_2219_, v_x_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
return v_res_2230_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2232_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2232_, 0, lean_box(0));
lean_closure_set(v___x_2232_, 1, lean_box(0));
lean_closure_set(v___x_2232_, 2, v___x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2233_, lean_object* v_pre_2234_, lean_object* v_post_2235_, uint8_t v_usedLetOnly_2236_, uint8_t v_skipConstInApp_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v_a_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; 
v___x_2243_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2244_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2243_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2244_);
v___x_2246_ = 0;
v___x_2247_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2234_, v_post_2235_, v_usedLetOnly_2236_, v_skipConstInApp_2237_, v___x_2246_, v_input_2233_, v_a_2245_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
lean_dec_ref(v___x_2247_);
v___x_2249_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2249_, 0, lean_box(0));
lean_closure_set(v___x_2249_, 1, lean_box(0));
lean_closure_set(v___x_2249_, 2, v_a_2245_);
v___x_2250_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2249_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; 
v_unused_2258_ = lean_ctor_get(v___x_2250_, 0);
lean_dec(v_unused_2258_);
v___x_2252_ = v___x_2250_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_dec(v___x_2250_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v_a_2248_);
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2248_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
else
{
lean_dec(v_a_2245_);
return v___x_2247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2259_, lean_object* v_pre_2260_, lean_object* v_post_2261_, lean_object* v_usedLetOnly_2262_, lean_object* v_skipConstInApp_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v_usedLetOnly_boxed_2269_; uint8_t v_skipConstInApp_boxed_2270_; lean_object* v_res_2271_; 
v_usedLetOnly_boxed_2269_ = lean_unbox(v_usedLetOnly_2262_);
v_skipConstInApp_boxed_2270_ = lean_unbox(v_skipConstInApp_2263_);
v_res_2271_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2259_, v_pre_2260_, v_post_2261_, v_usedLetOnly_boxed_2269_, v_skipConstInApp_boxed_2270_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_st_ref_get(v_val_2272_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object* v_val_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v_val_2280_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2287_, lean_object* v_val_2288_, lean_object* v_a_2289_, lean_object* v___x_2290_, lean_object* v_____r_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2297_ = lean_st_ref_take(v_val_2287_);
v___x_2298_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2288_, v_a_2289_, v___x_2297_);
v___x_2299_ = lean_st_ref_set(v_val_2287_, v___x_2298_);
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2290_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2302_, lean_object* v_val_2303_, lean_object* v_a_2304_, lean_object* v___x_2305_, lean_object* v_____r_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2302_, v_val_2303_, v_a_2304_, v___x_2305_, v_____r_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v_val_2303_);
lean_dec(v_val_2302_);
return v_res_2312_;
}
}
static uint64_t _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0(void){
_start:
{
uint8_t v___x_2313_; uint64_t v___x_2314_; 
v___x_2313_ = 2;
v___x_2314_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_upperBound_2315_, lean_object* v_val_2316_, lean_object* v_next_2317_, lean_object* v_params_2318_, lean_object* v___x_2319_, lean_object* v_val_2320_, lean_object* v_next_2321_, uint8_t v___x_2322_, lean_object* v_a_2323_, uint8_t v_b_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
uint8_t v_a_2331_; uint8_t v___x_2335_; 
v___x_2335_ = lean_nat_dec_lt(v_a_2323_, v_upperBound_2315_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec(v_a_2323_);
lean_dec(v_next_2321_);
lean_dec_ref(v___x_2319_);
v___x_2336_ = lean_box(v_b_2324_);
v___x_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2338_ = lean_st_ref_get(v_val_2316_);
v___x_2339_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2317_, v_a_2323_, v___x_2338_);
lean_dec(v___x_2338_);
if (v___x_2339_ == 0)
{
v_a_2331_ = v_b_2324_;
goto v___jp_2330_;
}
else
{
lean_object* v___x_2340_; uint8_t v_foApprox_2341_; uint8_t v_ctxApprox_2342_; uint8_t v_quasiPatternApprox_2343_; uint8_t v_constApprox_2344_; uint8_t v_isDefEqStuckEx_2345_; uint8_t v_unificationHints_2346_; uint8_t v_assignSyntheticOpaque_2347_; uint8_t v_offsetCnstrs_2348_; uint8_t v_transparency_2349_; uint8_t v_etaStruct_2350_; uint8_t v_univApprox_2351_; uint8_t v_iota_2352_; uint8_t v_beta_2353_; uint8_t v_proj_2354_; uint8_t v_zeta_2355_; uint8_t v_zetaDelta_2356_; uint8_t v_zetaUnused_2357_; uint8_t v_zetaHave_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2421_; 
v___x_2340_ = l_Lean_Meta_Context_config(v___y_2325_);
v_foApprox_2341_ = lean_ctor_get_uint8(v___x_2340_, 0);
v_ctxApprox_2342_ = lean_ctor_get_uint8(v___x_2340_, 1);
v_quasiPatternApprox_2343_ = lean_ctor_get_uint8(v___x_2340_, 2);
v_constApprox_2344_ = lean_ctor_get_uint8(v___x_2340_, 3);
v_isDefEqStuckEx_2345_ = lean_ctor_get_uint8(v___x_2340_, 4);
v_unificationHints_2346_ = lean_ctor_get_uint8(v___x_2340_, 5);
v_assignSyntheticOpaque_2347_ = lean_ctor_get_uint8(v___x_2340_, 7);
v_offsetCnstrs_2348_ = lean_ctor_get_uint8(v___x_2340_, 8);
v_transparency_2349_ = lean_ctor_get_uint8(v___x_2340_, 9);
v_etaStruct_2350_ = lean_ctor_get_uint8(v___x_2340_, 10);
v_univApprox_2351_ = lean_ctor_get_uint8(v___x_2340_, 11);
v_iota_2352_ = lean_ctor_get_uint8(v___x_2340_, 12);
v_beta_2353_ = lean_ctor_get_uint8(v___x_2340_, 13);
v_proj_2354_ = lean_ctor_get_uint8(v___x_2340_, 14);
v_zeta_2355_ = lean_ctor_get_uint8(v___x_2340_, 15);
v_zetaDelta_2356_ = lean_ctor_get_uint8(v___x_2340_, 16);
v_zetaUnused_2357_ = lean_ctor_get_uint8(v___x_2340_, 17);
v_zetaHave_2358_ = lean_ctor_get_uint8(v___x_2340_, 18);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2360_ = v___x_2340_;
v_isShared_2361_ = v_isSharedCheck_2421_;
goto v_resetjp_2359_;
}
else
{
lean_dec(v___x_2340_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2421_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
uint8_t v_trackZetaDelta_2362_; lean_object* v_zetaDeltaSet_2363_; lean_object* v_lctx_2364_; lean_object* v_localInstances_2365_; lean_object* v_defEqCtx_x3f_2366_; lean_object* v_synthPendingDepth_2367_; lean_object* v_canUnfold_x3f_2368_; uint8_t v_univApprox_2369_; uint8_t v_inTypeClassResolution_2370_; uint8_t v_cacheInferType_2371_; uint8_t v___x_2372_; lean_object* v___x_2374_; 
v_trackZetaDelta_2362_ = lean_ctor_get_uint8(v___y_2325_, sizeof(void*)*7);
v_zetaDeltaSet_2363_ = lean_ctor_get(v___y_2325_, 1);
v_lctx_2364_ = lean_ctor_get(v___y_2325_, 2);
v_localInstances_2365_ = lean_ctor_get(v___y_2325_, 3);
v_defEqCtx_x3f_2366_ = lean_ctor_get(v___y_2325_, 4);
v_synthPendingDepth_2367_ = lean_ctor_get(v___y_2325_, 5);
v_canUnfold_x3f_2368_ = lean_ctor_get(v___y_2325_, 6);
v_univApprox_2369_ = lean_ctor_get_uint8(v___y_2325_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2370_ = lean_ctor_get_uint8(v___y_2325_, sizeof(void*)*7 + 2);
v_cacheInferType_2371_ = lean_ctor_get_uint8(v___y_2325_, sizeof(void*)*7 + 3);
v___x_2372_ = 0;
if (v_isShared_2361_ == 0)
{
v___x_2374_ = v___x_2360_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 0, v_foApprox_2341_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 1, v_ctxApprox_2342_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 2, v_quasiPatternApprox_2343_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 3, v_constApprox_2344_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 4, v_isDefEqStuckEx_2345_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 5, v_unificationHints_2346_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 7, v_assignSyntheticOpaque_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 8, v_offsetCnstrs_2348_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 9, v_transparency_2349_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 10, v_etaStruct_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 11, v_univApprox_2351_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 12, v_iota_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 13, v_beta_2353_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 14, v_proj_2354_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 15, v_zeta_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 16, v_zetaDelta_2356_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 17, v_zetaUnused_2357_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, 18, v_zetaHave_2358_);
v___x_2374_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
uint64_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; uint8_t v_foApprox_2379_; uint8_t v_ctxApprox_2380_; uint8_t v_quasiPatternApprox_2381_; uint8_t v_constApprox_2382_; uint8_t v_isDefEqStuckEx_2383_; uint8_t v_unificationHints_2384_; uint8_t v_proofIrrelevance_2385_; uint8_t v_assignSyntheticOpaque_2386_; uint8_t v_offsetCnstrs_2387_; uint8_t v_etaStruct_2388_; uint8_t v_univApprox_2389_; uint8_t v_iota_2390_; uint8_t v_beta_2391_; uint8_t v_proj_2392_; uint8_t v_zeta_2393_; uint8_t v_zetaDelta_2394_; uint8_t v_zetaUnused_2395_; uint8_t v_zetaHave_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2419_; 
lean_ctor_set_uint8(v___x_2374_, 6, v___x_2372_);
v___x_2375_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2374_);
v___x_2376_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set_uint64(v___x_2376_, sizeof(void*)*1, v___x_2375_);
lean_inc(v_canUnfold_x3f_2368_);
lean_inc(v_synthPendingDepth_2367_);
lean_inc(v_defEqCtx_x3f_2366_);
lean_inc_ref(v_localInstances_2365_);
lean_inc_ref(v_lctx_2364_);
lean_inc(v_zetaDeltaSet_2363_);
v___x_2377_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v_zetaDeltaSet_2363_);
lean_ctor_set(v___x_2377_, 2, v_lctx_2364_);
lean_ctor_set(v___x_2377_, 3, v_localInstances_2365_);
lean_ctor_set(v___x_2377_, 4, v_defEqCtx_x3f_2366_);
lean_ctor_set(v___x_2377_, 5, v_synthPendingDepth_2367_);
lean_ctor_set(v___x_2377_, 6, v_canUnfold_x3f_2368_);
lean_ctor_set_uint8(v___x_2377_, sizeof(void*)*7, v_trackZetaDelta_2362_);
lean_ctor_set_uint8(v___x_2377_, sizeof(void*)*7 + 1, v_univApprox_2369_);
lean_ctor_set_uint8(v___x_2377_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2370_);
lean_ctor_set_uint8(v___x_2377_, sizeof(void*)*7 + 3, v_cacheInferType_2371_);
v___x_2378_ = l_Lean_Meta_Context_config(v___x_2377_);
v_foApprox_2379_ = lean_ctor_get_uint8(v___x_2378_, 0);
v_ctxApprox_2380_ = lean_ctor_get_uint8(v___x_2378_, 1);
v_quasiPatternApprox_2381_ = lean_ctor_get_uint8(v___x_2378_, 2);
v_constApprox_2382_ = lean_ctor_get_uint8(v___x_2378_, 3);
v_isDefEqStuckEx_2383_ = lean_ctor_get_uint8(v___x_2378_, 4);
v_unificationHints_2384_ = lean_ctor_get_uint8(v___x_2378_, 5);
v_proofIrrelevance_2385_ = lean_ctor_get_uint8(v___x_2378_, 6);
v_assignSyntheticOpaque_2386_ = lean_ctor_get_uint8(v___x_2378_, 7);
v_offsetCnstrs_2387_ = lean_ctor_get_uint8(v___x_2378_, 8);
v_etaStruct_2388_ = lean_ctor_get_uint8(v___x_2378_, 10);
v_univApprox_2389_ = lean_ctor_get_uint8(v___x_2378_, 11);
v_iota_2390_ = lean_ctor_get_uint8(v___x_2378_, 12);
v_beta_2391_ = lean_ctor_get_uint8(v___x_2378_, 13);
v_proj_2392_ = lean_ctor_get_uint8(v___x_2378_, 14);
v_zeta_2393_ = lean_ctor_get_uint8(v___x_2378_, 15);
v_zetaDelta_2394_ = lean_ctor_get_uint8(v___x_2378_, 16);
v_zetaUnused_2395_ = lean_ctor_get_uint8(v___x_2378_, 17);
v_zetaHave_2396_ = lean_ctor_get_uint8(v___x_2378_, 18);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2398_ = v___x_2378_;
v_isShared_2399_ = v_isSharedCheck_2419_;
goto v_resetjp_2397_;
}
else
{
lean_dec(v___x_2378_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2419_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; uint8_t v___x_2401_; lean_object* v_config_2403_; 
v___x_2400_ = lean_array_fget_borrowed(v_params_2318_, v_a_2323_);
v___x_2401_ = 2;
if (v_isShared_2399_ == 0)
{
v_config_2403_ = v___x_2398_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 0, v_foApprox_2379_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 1, v_ctxApprox_2380_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 2, v_quasiPatternApprox_2381_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 3, v_constApprox_2382_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 4, v_isDefEqStuckEx_2383_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 5, v_unificationHints_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 6, v_proofIrrelevance_2385_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 7, v_assignSyntheticOpaque_2386_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 8, v_offsetCnstrs_2387_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 10, v_etaStruct_2388_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 11, v_univApprox_2389_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 12, v_iota_2390_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 13, v_beta_2391_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 14, v_proj_2392_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 15, v_zeta_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 16, v_zetaDelta_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 17, v_zetaUnused_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, 18, v_zetaHave_2396_);
v_config_2403_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
uint64_t v___x_2404_; uint64_t v___x_2405_; uint64_t v___x_2406_; uint64_t v___x_2407_; uint64_t v___x_2408_; uint64_t v_key_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
lean_ctor_set_uint8(v_config_2403_, 9, v___x_2401_);
v___x_2404_ = l_Lean_Meta_Context_configKey(v___x_2377_);
lean_dec_ref(v___x_2377_);
v___x_2405_ = 2ULL;
v___x_2406_ = lean_uint64_shift_right(v___x_2404_, v___x_2405_);
v___x_2407_ = lean_uint64_shift_left(v___x_2406_, v___x_2405_);
v___x_2408_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0);
v_key_2409_ = lean_uint64_lor(v___x_2407_, v___x_2408_);
v___x_2410_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2410_, 0, v_config_2403_);
lean_ctor_set_uint64(v___x_2410_, sizeof(void*)*1, v_key_2409_);
lean_inc(v_canUnfold_x3f_2368_);
lean_inc(v_synthPendingDepth_2367_);
lean_inc(v_defEqCtx_x3f_2366_);
lean_inc_ref(v_localInstances_2365_);
lean_inc_ref(v_lctx_2364_);
lean_inc(v_zetaDeltaSet_2363_);
v___x_2411_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v_zetaDeltaSet_2363_);
lean_ctor_set(v___x_2411_, 2, v_lctx_2364_);
lean_ctor_set(v___x_2411_, 3, v_localInstances_2365_);
lean_ctor_set(v___x_2411_, 4, v_defEqCtx_x3f_2366_);
lean_ctor_set(v___x_2411_, 5, v_synthPendingDepth_2367_);
lean_ctor_set(v___x_2411_, 6, v_canUnfold_x3f_2368_);
lean_ctor_set_uint8(v___x_2411_, sizeof(void*)*7, v_trackZetaDelta_2362_);
lean_ctor_set_uint8(v___x_2411_, sizeof(void*)*7 + 1, v_univApprox_2369_);
lean_ctor_set_uint8(v___x_2411_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2370_);
lean_ctor_set_uint8(v___x_2411_, sizeof(void*)*7 + 3, v_cacheInferType_2371_);
lean_inc_ref(v___x_2319_);
lean_inc(v___x_2400_);
v___x_2412_ = l_Lean_Meta_isExprDefEq(v___x_2400_, v___x_2319_, v___x_2411_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec_ref(v___x_2411_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; uint8_t v___x_2414_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref(v___x_2412_);
v___x_2414_ = lean_unbox(v_a_2413_);
lean_dec(v_a_2413_);
if (v___x_2414_ == 0)
{
v_a_2331_ = v_b_2324_;
goto v___jp_2330_;
}
else
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = lean_st_ref_take(v_val_2316_);
lean_inc(v_a_2323_);
lean_inc(v_next_2321_);
v___x_2416_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2320_, v_next_2321_, v_next_2317_, v_a_2323_, v___x_2415_);
v___x_2417_ = lean_st_ref_set(v_val_2316_, v___x_2416_);
v_a_2331_ = v___x_2322_;
goto v___jp_2330_;
}
}
else
{
lean_dec(v_a_2323_);
lean_dec(v_next_2321_);
lean_dec_ref(v___x_2319_);
return v___x_2412_;
}
}
}
}
}
}
}
v___jp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_unsigned_to_nat(1u);
v___x_2333_ = lean_nat_add(v_a_2323_, v___x_2332_);
lean_dec(v_a_2323_);
v_a_2323_ = v___x_2333_;
v_b_2324_ = v_a_2331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_upperBound_2422_, lean_object* v_val_2423_, lean_object* v_next_2424_, lean_object* v_params_2425_, lean_object* v___x_2426_, lean_object* v_val_2427_, lean_object* v_next_2428_, lean_object* v___x_2429_, lean_object* v_a_2430_, lean_object* v_b_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
uint8_t v___x_41291__boxed_2437_; uint8_t v_b_boxed_2438_; lean_object* v_res_2439_; 
v___x_41291__boxed_2437_ = lean_unbox(v___x_2429_);
v_b_boxed_2438_ = lean_unbox(v_b_2431_);
v_res_2439_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_2422_, v_val_2423_, v_next_2424_, v_params_2425_, v___x_2426_, v_val_2427_, v_next_2428_, v___x_41291__boxed_2437_, v_a_2430_, v_b_boxed_2438_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v_val_2427_);
lean_dec_ref(v_params_2425_);
lean_dec(v_next_2424_);
lean_dec(v_val_2423_);
lean_dec(v_upperBound_2422_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3_spec__3(lean_object* v_msgData_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___x_2446_; lean_object* v_env_2447_; lean_object* v___x_2448_; lean_object* v_mctx_2449_; lean_object* v_lctx_2450_; lean_object* v_options_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2446_ = lean_st_ref_get(v___y_2444_);
v_env_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc_ref(v_env_2447_);
lean_dec(v___x_2446_);
v___x_2448_ = lean_st_ref_get(v___y_2442_);
v_mctx_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc_ref(v_mctx_2449_);
lean_dec(v___x_2448_);
v_lctx_2450_ = lean_ctor_get(v___y_2441_, 2);
v_options_2451_ = lean_ctor_get(v___y_2443_, 2);
lean_inc_ref(v_options_2451_);
lean_inc_ref(v_lctx_2450_);
v___x_2452_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2452_, 0, v_env_2447_);
lean_ctor_set(v___x_2452_, 1, v_mctx_2449_);
lean_ctor_set(v___x_2452_, 2, v_lctx_2450_);
lean_ctor_set(v___x_2452_, 3, v_options_2451_);
v___x_2453_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
lean_ctor_set(v___x_2453_, 1, v_msgData_2440_);
v___x_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3_spec__3___boxed(lean_object* v_msgData_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3_spec__3(v_msgData_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
return v_res_2461_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2462_; double v___x_2463_; 
v___x_2462_ = lean_unsigned_to_nat(0u);
v___x_2463_ = lean_float_of_nat(v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v_cls_2467_, lean_object* v_msg_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v_ref_2474_; lean_object* v___x_2475_; lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2520_; 
v_ref_2474_ = lean_ctor_get(v___y_2471_, 5);
v___x_2475_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3_spec__3(v_msg_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2478_ = v___x_2475_;
v_isShared_2479_ = v_isSharedCheck_2520_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2475_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2520_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; lean_object* v_traceState_2481_; lean_object* v_env_2482_; lean_object* v_nextMacroScope_2483_; lean_object* v_ngen_2484_; lean_object* v_auxDeclNGen_2485_; lean_object* v_cache_2486_; lean_object* v_messages_2487_; lean_object* v_infoState_2488_; lean_object* v_snapshotTasks_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2519_; 
v___x_2480_ = lean_st_ref_take(v___y_2472_);
v_traceState_2481_ = lean_ctor_get(v___x_2480_, 4);
v_env_2482_ = lean_ctor_get(v___x_2480_, 0);
v_nextMacroScope_2483_ = lean_ctor_get(v___x_2480_, 1);
v_ngen_2484_ = lean_ctor_get(v___x_2480_, 2);
v_auxDeclNGen_2485_ = lean_ctor_get(v___x_2480_, 3);
v_cache_2486_ = lean_ctor_get(v___x_2480_, 5);
v_messages_2487_ = lean_ctor_get(v___x_2480_, 6);
v_infoState_2488_ = lean_ctor_get(v___x_2480_, 7);
v_snapshotTasks_2489_ = lean_ctor_get(v___x_2480_, 8);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2491_ = v___x_2480_;
v_isShared_2492_ = v_isSharedCheck_2519_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_snapshotTasks_2489_);
lean_inc(v_infoState_2488_);
lean_inc(v_messages_2487_);
lean_inc(v_cache_2486_);
lean_inc(v_traceState_2481_);
lean_inc(v_auxDeclNGen_2485_);
lean_inc(v_ngen_2484_);
lean_inc(v_nextMacroScope_2483_);
lean_inc(v_env_2482_);
lean_dec(v___x_2480_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2519_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
uint64_t v_tid_2493_; lean_object* v_traces_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2518_; 
v_tid_2493_ = lean_ctor_get_uint64(v_traceState_2481_, sizeof(void*)*1);
v_traces_2494_ = lean_ctor_get(v_traceState_2481_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v_traceState_2481_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2496_ = v_traceState_2481_;
v_isShared_2497_ = v_isSharedCheck_2518_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_traces_2494_);
lean_dec(v_traceState_2481_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2518_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; double v___x_2499_; uint8_t v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2498_ = lean_box(0);
v___x_2499_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__0);
v___x_2500_ = 0;
v___x_2501_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__1));
v___x_2502_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2502_, 0, v_cls_2467_);
lean_ctor_set(v___x_2502_, 1, v___x_2498_);
lean_ctor_set(v___x_2502_, 2, v___x_2501_);
lean_ctor_set_float(v___x_2502_, sizeof(void*)*3, v___x_2499_);
lean_ctor_set_float(v___x_2502_, sizeof(void*)*3 + 8, v___x_2499_);
lean_ctor_set_uint8(v___x_2502_, sizeof(void*)*3 + 16, v___x_2500_);
v___x_2503_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___closed__2));
v___x_2504_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2502_);
lean_ctor_set(v___x_2504_, 1, v_a_2476_);
lean_ctor_set(v___x_2504_, 2, v___x_2503_);
lean_inc(v_ref_2474_);
v___x_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2505_, 0, v_ref_2474_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = l_Lean_PersistentArray_push___redArg(v_traces_2494_, v___x_2505_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v___x_2506_);
v___x_2508_ = v___x_2496_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2506_);
lean_ctor_set_uint64(v_reuseFailAlloc_2517_, sizeof(void*)*1, v_tid_2493_);
v___x_2508_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2510_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 4, v___x_2508_);
v___x_2510_ = v___x_2491_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_env_2482_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_nextMacroScope_2483_);
lean_ctor_set(v_reuseFailAlloc_2516_, 2, v_ngen_2484_);
lean_ctor_set(v_reuseFailAlloc_2516_, 3, v_auxDeclNGen_2485_);
lean_ctor_set(v_reuseFailAlloc_2516_, 4, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2516_, 5, v_cache_2486_);
lean_ctor_set(v_reuseFailAlloc_2516_, 6, v_messages_2487_);
lean_ctor_set(v_reuseFailAlloc_2516_, 7, v_infoState_2488_);
lean_ctor_set(v_reuseFailAlloc_2516_, 8, v_snapshotTasks_2489_);
v___x_2510_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2511_ = lean_st_ref_set(v___y_2472_, v___x_2510_);
v___x_2512_ = lean_box(0);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v___x_2512_);
v___x_2514_ = v___x_2478_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v_cls_2521_, lean_object* v_msg_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(v_cls_2521_, v_msg_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
return v_res_2528_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__4));
v___x_2538_ = l_Lean_stringToMessageData(v___x_2537_);
return v___x_2538_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2540_ = l_Lean_stringToMessageData(v___x_2539_);
return v___x_2540_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2543_ = l_Lean_stringToMessageData(v___x_2542_);
return v___x_2543_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9));
v___x_2546_ = l_Lean_stringToMessageData(v___x_2545_);
return v___x_2546_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11));
v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13));
v___x_2552_ = l_Lean_stringToMessageData(v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2556_, lean_object* v_val_2557_, lean_object* v_upperBound_2558_, lean_object* v_args_2559_, lean_object* v_e_2560_, lean_object* v_next_2561_, lean_object* v_params_2562_, lean_object* v___x_2563_, uint8_t v___x_2564_, lean_object* v_a_2565_, lean_object* v_b_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_a_2573_; lean_object* v___y_2578_; uint8_t v___x_2597_; 
v___x_2597_ = lean_nat_dec_lt(v_a_2565_, v_upperBound_2558_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; 
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
v___x_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2598_, 0, v_b_2566_);
return v___x_2598_;
}
else
{
lean_object* v___x_2599_; 
v___x_2599_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2556_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref(v___x_2599_);
v___x_2601_ = lean_box(0);
v___x_2602_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2557_, v_a_2565_, v_a_2600_);
lean_dec(v_a_2600_);
if (v___x_2602_ == 0)
{
v_a_2573_ = v___x_2601_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2603_ = lean_array_get_size(v_args_2559_);
v___x_2604_ = lean_nat_dec_lt(v_a_2565_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2606_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg(v___x_2605_, v___y_2569_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; uint8_t v___x_2608_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref(v___x_2606_);
v___x_2608_ = lean_unbox(v_a_2607_);
lean_dec(v_a_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; 
lean_inc(v_a_2565_);
v___x_2609_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2556_, v_val_2557_, v_a_2565_, v___x_2601_, v___x_2601_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
v___y_2578_ = v___x_2609_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2610_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5);
lean_inc(v_val_2557_);
v___x_2611_ = l_Nat_reprFast(v_val_2557_);
v___x_2612_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
v___x_2613_ = l_Lean_MessageData_ofFormat(v___x_2612_);
v___x_2614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2610_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2614_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
lean_inc(v_a_2565_);
v___x_2617_ = l_Nat_reprFast(v_a_2565_);
v___x_2618_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
v___x_2619_ = l_Lean_MessageData_ofFormat(v___x_2618_);
lean_inc_ref(v___x_2619_);
v___x_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2616_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
v___x_2622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2620_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
lean_inc_ref(v_e_2560_);
v___x_2623_ = l_Lean_MessageData_ofExpr(v_e_2560_);
v___x_2624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2622_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10);
v___x_2626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2624_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v___x_2619_);
v___x_2628_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2605_, v___x_2627_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2630_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref(v___x_2628_);
lean_inc(v_a_2565_);
v___x_2630_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2556_, v_val_2557_, v_a_2565_, v___x_2601_, v_a_2629_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
v___y_2578_ = v___x_2630_;
goto v___jp_2577_;
}
else
{
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
return v___x_2628_;
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
v_a_2631_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2606_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2606_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v___x_2639_; 
v___x_2639_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2556_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref(v___x_2639_);
v___x_2641_ = lean_array_fget_borrowed(v_args_2559_, v_a_2565_);
v___x_2642_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2557_, v_a_2565_, v_next_2561_, v_a_2640_);
lean_dec(v_a_2640_);
if (lean_obj_tag(v___x_2642_) == 1)
{
lean_object* v_val_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2776_; 
v_val_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2776_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_val_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2776_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; uint8_t v_foApprox_2648_; uint8_t v_ctxApprox_2649_; uint8_t v_quasiPatternApprox_2650_; uint8_t v_constApprox_2651_; uint8_t v_isDefEqStuckEx_2652_; uint8_t v_unificationHints_2653_; uint8_t v_assignSyntheticOpaque_2654_; uint8_t v_offsetCnstrs_2655_; uint8_t v_transparency_2656_; uint8_t v_etaStruct_2657_; uint8_t v_univApprox_2658_; uint8_t v_iota_2659_; uint8_t v_beta_2660_; uint8_t v_proj_2661_; uint8_t v_zeta_2662_; uint8_t v_zetaDelta_2663_; uint8_t v_zetaUnused_2664_; uint8_t v_zetaHave_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2775_; 
v___x_2647_ = l_Lean_Meta_Context_config(v___y_2567_);
v_foApprox_2648_ = lean_ctor_get_uint8(v___x_2647_, 0);
v_ctxApprox_2649_ = lean_ctor_get_uint8(v___x_2647_, 1);
v_quasiPatternApprox_2650_ = lean_ctor_get_uint8(v___x_2647_, 2);
v_constApprox_2651_ = lean_ctor_get_uint8(v___x_2647_, 3);
v_isDefEqStuckEx_2652_ = lean_ctor_get_uint8(v___x_2647_, 4);
v_unificationHints_2653_ = lean_ctor_get_uint8(v___x_2647_, 5);
v_assignSyntheticOpaque_2654_ = lean_ctor_get_uint8(v___x_2647_, 7);
v_offsetCnstrs_2655_ = lean_ctor_get_uint8(v___x_2647_, 8);
v_transparency_2656_ = lean_ctor_get_uint8(v___x_2647_, 9);
v_etaStruct_2657_ = lean_ctor_get_uint8(v___x_2647_, 10);
v_univApprox_2658_ = lean_ctor_get_uint8(v___x_2647_, 11);
v_iota_2659_ = lean_ctor_get_uint8(v___x_2647_, 12);
v_beta_2660_ = lean_ctor_get_uint8(v___x_2647_, 13);
v_proj_2661_ = lean_ctor_get_uint8(v___x_2647_, 14);
v_zeta_2662_ = lean_ctor_get_uint8(v___x_2647_, 15);
v_zetaDelta_2663_ = lean_ctor_get_uint8(v___x_2647_, 16);
v_zetaUnused_2664_ = lean_ctor_get_uint8(v___x_2647_, 17);
v_zetaHave_2665_ = lean_ctor_get_uint8(v___x_2647_, 18);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2667_ = v___x_2647_;
v_isShared_2668_ = v_isSharedCheck_2775_;
goto v_resetjp_2666_;
}
else
{
lean_dec(v___x_2647_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2775_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
uint8_t v_trackZetaDelta_2669_; lean_object* v_zetaDeltaSet_2670_; lean_object* v_lctx_2671_; lean_object* v_localInstances_2672_; lean_object* v_defEqCtx_x3f_2673_; lean_object* v_synthPendingDepth_2674_; lean_object* v_canUnfold_x3f_2675_; uint8_t v_univApprox_2676_; uint8_t v_inTypeClassResolution_2677_; uint8_t v_cacheInferType_2678_; uint8_t v___x_2679_; lean_object* v___x_2681_; 
v_trackZetaDelta_2669_ = lean_ctor_get_uint8(v___y_2567_, sizeof(void*)*7);
v_zetaDeltaSet_2670_ = lean_ctor_get(v___y_2567_, 1);
v_lctx_2671_ = lean_ctor_get(v___y_2567_, 2);
v_localInstances_2672_ = lean_ctor_get(v___y_2567_, 3);
v_defEqCtx_x3f_2673_ = lean_ctor_get(v___y_2567_, 4);
v_synthPendingDepth_2674_ = lean_ctor_get(v___y_2567_, 5);
v_canUnfold_x3f_2675_ = lean_ctor_get(v___y_2567_, 6);
v_univApprox_2676_ = lean_ctor_get_uint8(v___y_2567_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2677_ = lean_ctor_get_uint8(v___y_2567_, sizeof(void*)*7 + 2);
v_cacheInferType_2678_ = lean_ctor_get_uint8(v___y_2567_, sizeof(void*)*7 + 3);
v___x_2679_ = 0;
if (v_isShared_2668_ == 0)
{
v___x_2681_ = v___x_2667_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 0, v_foApprox_2648_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 1, v_ctxApprox_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 2, v_quasiPatternApprox_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 3, v_constApprox_2651_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 4, v_isDefEqStuckEx_2652_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 5, v_unificationHints_2653_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 7, v_assignSyntheticOpaque_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 8, v_offsetCnstrs_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 9, v_transparency_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 10, v_etaStruct_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 11, v_univApprox_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 12, v_iota_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 13, v_beta_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 14, v_proj_2661_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 15, v_zeta_2662_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 16, v_zetaDelta_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 17, v_zetaUnused_2664_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 18, v_zetaHave_2665_);
v___x_2681_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
uint64_t v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v_foApprox_2686_; uint8_t v_ctxApprox_2687_; uint8_t v_quasiPatternApprox_2688_; uint8_t v_constApprox_2689_; uint8_t v_isDefEqStuckEx_2690_; uint8_t v_unificationHints_2691_; uint8_t v_proofIrrelevance_2692_; uint8_t v_assignSyntheticOpaque_2693_; uint8_t v_offsetCnstrs_2694_; uint8_t v_etaStruct_2695_; uint8_t v_univApprox_2696_; uint8_t v_iota_2697_; uint8_t v_beta_2698_; uint8_t v_proj_2699_; uint8_t v_zeta_2700_; uint8_t v_zetaDelta_2701_; uint8_t v_zetaUnused_2702_; uint8_t v_zetaHave_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2773_; 
lean_ctor_set_uint8(v___x_2681_, 6, v___x_2679_);
v___x_2682_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2681_);
v___x_2683_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2683_, 0, v___x_2681_);
lean_ctor_set_uint64(v___x_2683_, sizeof(void*)*1, v___x_2682_);
lean_inc(v_canUnfold_x3f_2675_);
lean_inc(v_synthPendingDepth_2674_);
lean_inc(v_defEqCtx_x3f_2673_);
lean_inc_ref(v_localInstances_2672_);
lean_inc_ref(v_lctx_2671_);
lean_inc(v_zetaDeltaSet_2670_);
v___x_2684_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
lean_ctor_set(v___x_2684_, 1, v_zetaDeltaSet_2670_);
lean_ctor_set(v___x_2684_, 2, v_lctx_2671_);
lean_ctor_set(v___x_2684_, 3, v_localInstances_2672_);
lean_ctor_set(v___x_2684_, 4, v_defEqCtx_x3f_2673_);
lean_ctor_set(v___x_2684_, 5, v_synthPendingDepth_2674_);
lean_ctor_set(v___x_2684_, 6, v_canUnfold_x3f_2675_);
lean_ctor_set_uint8(v___x_2684_, sizeof(void*)*7, v_trackZetaDelta_2669_);
lean_ctor_set_uint8(v___x_2684_, sizeof(void*)*7 + 1, v_univApprox_2676_);
lean_ctor_set_uint8(v___x_2684_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2677_);
lean_ctor_set_uint8(v___x_2684_, sizeof(void*)*7 + 3, v_cacheInferType_2678_);
v___x_2685_ = l_Lean_Meta_Context_config(v___x_2684_);
v_foApprox_2686_ = lean_ctor_get_uint8(v___x_2685_, 0);
v_ctxApprox_2687_ = lean_ctor_get_uint8(v___x_2685_, 1);
v_quasiPatternApprox_2688_ = lean_ctor_get_uint8(v___x_2685_, 2);
v_constApprox_2689_ = lean_ctor_get_uint8(v___x_2685_, 3);
v_isDefEqStuckEx_2690_ = lean_ctor_get_uint8(v___x_2685_, 4);
v_unificationHints_2691_ = lean_ctor_get_uint8(v___x_2685_, 5);
v_proofIrrelevance_2692_ = lean_ctor_get_uint8(v___x_2685_, 6);
v_assignSyntheticOpaque_2693_ = lean_ctor_get_uint8(v___x_2685_, 7);
v_offsetCnstrs_2694_ = lean_ctor_get_uint8(v___x_2685_, 8);
v_etaStruct_2695_ = lean_ctor_get_uint8(v___x_2685_, 10);
v_univApprox_2696_ = lean_ctor_get_uint8(v___x_2685_, 11);
v_iota_2697_ = lean_ctor_get_uint8(v___x_2685_, 12);
v_beta_2698_ = lean_ctor_get_uint8(v___x_2685_, 13);
v_proj_2699_ = lean_ctor_get_uint8(v___x_2685_, 14);
v_zeta_2700_ = lean_ctor_get_uint8(v___x_2685_, 15);
v_zetaDelta_2701_ = lean_ctor_get_uint8(v___x_2685_, 16);
v_zetaUnused_2702_ = lean_ctor_get_uint8(v___x_2685_, 17);
v_zetaHave_2703_ = lean_ctor_get_uint8(v___x_2685_, 18);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2705_ = v___x_2685_;
v_isShared_2706_ = v_isSharedCheck_2773_;
goto v_resetjp_2704_;
}
else
{
lean_dec(v___x_2685_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2773_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; lean_object* v_config_2711_; 
v___x_2707_ = l_Lean_instInhabitedExpr;
v___x_2708_ = lean_array_get_borrowed(v___x_2707_, v_params_2562_, v_val_2643_);
lean_dec(v_val_2643_);
v___x_2709_ = 2;
if (v_isShared_2706_ == 0)
{
v_config_2711_ = v___x_2705_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 0, v_foApprox_2686_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 1, v_ctxApprox_2687_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 2, v_quasiPatternApprox_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 3, v_constApprox_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 4, v_isDefEqStuckEx_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 5, v_unificationHints_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 6, v_proofIrrelevance_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 7, v_assignSyntheticOpaque_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 8, v_offsetCnstrs_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 10, v_etaStruct_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 11, v_univApprox_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 12, v_iota_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 13, v_beta_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 14, v_proj_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 15, v_zeta_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 16, v_zetaDelta_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 17, v_zetaUnused_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 18, v_zetaHave_2703_);
v_config_2711_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
uint64_t v___x_2712_; uint64_t v___x_2713_; uint64_t v___x_2714_; uint64_t v___x_2715_; uint64_t v___x_2716_; uint64_t v_key_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_ctor_set_uint8(v_config_2711_, 9, v___x_2709_);
v___x_2712_ = l_Lean_Meta_Context_configKey(v___x_2684_);
lean_dec_ref(v___x_2684_);
v___x_2713_ = 2ULL;
v___x_2714_ = lean_uint64_shift_right(v___x_2712_, v___x_2713_);
v___x_2715_ = lean_uint64_shift_left(v___x_2714_, v___x_2713_);
v___x_2716_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0);
v_key_2717_ = lean_uint64_lor(v___x_2715_, v___x_2716_);
v___x_2718_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2718_, 0, v_config_2711_);
lean_ctor_set_uint64(v___x_2718_, sizeof(void*)*1, v_key_2717_);
lean_inc(v_canUnfold_x3f_2675_);
lean_inc(v_synthPendingDepth_2674_);
lean_inc(v_defEqCtx_x3f_2673_);
lean_inc_ref(v_localInstances_2672_);
lean_inc_ref(v_lctx_2671_);
lean_inc(v_zetaDeltaSet_2670_);
v___x_2719_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v_zetaDeltaSet_2670_);
lean_ctor_set(v___x_2719_, 2, v_lctx_2671_);
lean_ctor_set(v___x_2719_, 3, v_localInstances_2672_);
lean_ctor_set(v___x_2719_, 4, v_defEqCtx_x3f_2673_);
lean_ctor_set(v___x_2719_, 5, v_synthPendingDepth_2674_);
lean_ctor_set(v___x_2719_, 6, v_canUnfold_x3f_2675_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*7, v_trackZetaDelta_2669_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*7 + 1, v_univApprox_2676_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2677_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*7 + 3, v_cacheInferType_2678_);
lean_inc(v___x_2641_);
lean_inc(v___x_2708_);
v___x_2720_ = l_Lean_Meta_isExprDefEq(v___x_2708_, v___x_2641_, v___x_2719_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec_ref(v___x_2719_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; uint8_t v___x_2722_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref(v___x_2720_);
v___x_2722_ = lean_unbox(v_a_2721_);
lean_dec(v_a_2721_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2724_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg(v___x_2723_, v___y_2569_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; uint8_t v___x_2726_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref(v___x_2724_);
v___x_2726_ = lean_unbox(v_a_2725_);
lean_dec(v_a_2725_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; 
lean_del_object(v___x_2645_);
lean_inc(v_a_2565_);
v___x_2727_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2556_, v_val_2557_, v_a_2565_, v___x_2601_, v___x_2601_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
v___y_2578_ = v___x_2727_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2728_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5);
lean_inc(v_val_2557_);
v___x_2729_ = l_Nat_reprFast(v_val_2557_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set_tag(v___x_2645_, 3);
lean_ctor_set(v___x_2645_, 0, v___x_2729_);
v___x_2731_ = v___x_2645_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2732_ = l_Lean_MessageData_ofFormat(v___x_2731_);
v___x_2733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2728_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
v___x_2734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
lean_inc(v_a_2565_);
v___x_2736_ = l_Nat_reprFast(v_a_2565_);
v___x_2737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
v___x_2738_ = l_Lean_MessageData_ofFormat(v___x_2737_);
v___x_2739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2735_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
v___x_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
lean_inc_ref(v_e_2560_);
v___x_2742_ = l_Lean_MessageData_ofExpr(v_e_2560_);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12);
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
lean_inc(v___x_2708_);
v___x_2746_ = l_Lean_MessageData_ofExpr(v___x_2708_);
v___x_2747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
lean_inc(v___x_2641_);
v___x_2750_ = l_Lean_MessageData_ofExpr(v___x_2641_);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2723_, v___x_2751_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref(v___x_2752_);
lean_inc(v_a_2565_);
v___x_2754_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2556_, v_val_2557_, v_a_2565_, v___x_2601_, v_a_2753_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
v___y_2578_ = v___x_2754_;
goto v___jp_2577_;
}
else
{
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
return v___x_2752_;
}
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_del_object(v___x_2645_);
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
v_a_2756_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2724_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2724_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
else
{
lean_del_object(v___x_2645_);
v_a_2573_ = v___x_2601_;
goto v___jp_2572_;
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_del_object(v___x_2645_);
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
v_a_2764_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2720_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2720_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
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
lean_object* v___x_2777_; uint8_t v___x_2778_; lean_object* v___x_2779_; 
lean_dec(v___x_2642_);
v___x_2777_ = lean_unsigned_to_nat(0u);
v___x_2778_ = 0;
lean_inc(v_a_2565_);
lean_inc(v___x_2641_);
v___x_2779_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v___x_2563_, v_val_2556_, v_next_2561_, v_params_2562_, v___x_2641_, v_val_2557_, v_a_2565_, v___x_2564_, v___x_2777_, v___x_2778_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; uint8_t v___x_2781_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref(v___x_2779_);
v___x_2781_ = lean_unbox(v_a_2780_);
lean_dec(v_a_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2783_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg(v___x_2782_, v___y_2569_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; uint8_t v___x_2785_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref(v___x_2783_);
v___x_2785_ = lean_unbox(v_a_2784_);
lean_dec(v_a_2784_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; 
lean_inc(v_a_2565_);
v___x_2786_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2556_, v_val_2557_, v_a_2565_, v___x_2601_, v___x_2601_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
v___y_2578_ = v___x_2786_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2787_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5);
lean_inc(v_val_2557_);
v___x_2788_ = l_Nat_reprFast(v_val_2557_);
v___x_2789_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
v___x_2790_ = l_Lean_MessageData_ofFormat(v___x_2789_);
v___x_2791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2787_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
lean_inc(v_a_2565_);
v___x_2794_ = l_Nat_reprFast(v_a_2565_);
v___x_2795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2794_);
v___x_2796_ = l_Lean_MessageData_ofFormat(v___x_2795_);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2793_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
lean_inc_ref(v_e_2560_);
v___x_2800_ = l_Lean_MessageData_ofExpr(v_e_2560_);
v___x_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12);
v___x_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2801_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
lean_inc(v___x_2641_);
v___x_2804_ = l_Lean_MessageData_ofExpr(v___x_2641_);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16);
v___x_2807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2805_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2782_, v___x_2807_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref(v___x_2808_);
lean_inc(v_a_2565_);
v___x_2810_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2556_, v_val_2557_, v_a_2565_, v___x_2601_, v_a_2809_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
v___y_2578_ = v___x_2810_;
goto v___jp_2577_;
}
else
{
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
return v___x_2808_;
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
v_a_2811_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2783_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2783_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
else
{
v_a_2573_ = v___x_2601_;
goto v___jp_2572_;
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
v_a_2819_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2779_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2779_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
v_a_2827_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2639_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2639_);
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
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
v_a_2835_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2599_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2599_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
v___jp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_unsigned_to_nat(1u);
v___x_2575_ = lean_nat_add(v_a_2565_, v___x_2574_);
lean_dec(v_a_2565_);
v_a_2565_ = v___x_2575_;
v_b_2566_ = v_a_2573_;
goto _start;
}
v___jp_2577_:
{
if (lean_obj_tag(v___y_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2588_; 
v_a_2579_ = lean_ctor_get(v___y_2578_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___y_2578_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2581_ = v___y_2578_;
v_isShared_2582_ = v_isSharedCheck_2588_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___y_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2588_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
if (lean_obj_tag(v_a_2579_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2585_; 
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
v_a_2583_ = lean_ctor_get(v_a_2579_, 0);
lean_inc(v_a_2583_);
lean_dec_ref(v_a_2579_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v_a_2583_);
v___x_2585_ = v___x_2581_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
else
{
lean_object* v_a_2587_; 
lean_del_object(v___x_2581_);
v_a_2587_ = lean_ctor_get(v_a_2579_, 0);
lean_inc(v_a_2587_);
lean_dec_ref(v_a_2579_);
v_a_2573_ = v_a_2587_;
goto v___jp_2572_;
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v_a_2565_);
lean_dec_ref(v_e_2560_);
lean_dec(v_val_2557_);
v_a_2589_ = lean_ctor_get(v___y_2578_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___y_2578_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___y_2578_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___y_2578_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2843_, lean_object* v_val_2844_, lean_object* v_upperBound_2845_, lean_object* v_args_2846_, lean_object* v_e_2847_, lean_object* v_next_2848_, lean_object* v_params_2849_, lean_object* v___x_2850_, lean_object* v___x_2851_, lean_object* v_a_2852_, lean_object* v_b_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
uint8_t v___x_41630__boxed_2859_; lean_object* v_res_2860_; 
v___x_41630__boxed_2859_ = lean_unbox(v___x_2851_);
v_res_2860_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2843_, v_val_2844_, v_upperBound_2845_, v_args_2846_, v_e_2847_, v_next_2848_, v_params_2849_, v___x_2850_, v___x_41630__boxed_2859_, v_a_2852_, v_b_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___x_2850_);
lean_dec_ref(v_params_2849_);
lean_dec(v_next_2848_);
lean_dec_ref(v_args_2846_);
lean_dec(v_upperBound_2845_);
lean_dec(v_val_2843_);
return v_res_2860_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___lam__0(lean_object* v___x_2861_, lean_object* v_x_2862_){
_start:
{
lean_object* v_declName_2863_; uint8_t v___x_2864_; 
v_declName_2863_ = lean_ctor_get(v_x_2862_, 3);
v___x_2864_ = lean_name_eq(v_declName_2863_, v___x_2861_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___lam__0___boxed(lean_object* v___x_2865_, lean_object* v_x_2866_){
_start:
{
uint8_t v_res_2867_; lean_object* v_r_2868_; 
v_res_2867_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___lam__0(v___x_2865_, v_x_2866_);
lean_dec_ref(v_x_2866_);
lean_dec(v___x_2865_);
v_r_2868_ = lean_box(v_res_2867_);
return v_r_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2871_, lean_object* v___x_2872_, lean_object* v_val_2873_, lean_object* v_e_2874_, lean_object* v_next_2875_, lean_object* v_params_2876_, lean_object* v___x_2877_, lean_object* v_x_2878_, lean_object* v_x_2879_, lean_object* v_x_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
if (lean_obj_tag(v_x_2878_) == 5)
{
lean_object* v_fn_2886_; lean_object* v_arg_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_fn_2886_ = lean_ctor_get(v_x_2878_, 0);
lean_inc_ref(v_fn_2886_);
v_arg_2887_ = lean_ctor_get(v_x_2878_, 1);
lean_inc_ref(v_arg_2887_);
lean_dec_ref(v_x_2878_);
v___x_2888_ = lean_array_set(v_x_2879_, v_x_2880_, v_arg_2887_);
v___x_2889_ = lean_unsigned_to_nat(1u);
v___x_2890_ = lean_nat_sub(v_x_2880_, v___x_2889_);
lean_dec(v_x_2880_);
v_x_2878_ = v_fn_2886_;
v_x_2879_ = v___x_2888_;
v_x_2880_ = v___x_2890_;
goto _start;
}
else
{
uint8_t v___x_2892_; 
lean_dec(v_x_2880_);
v___x_2892_ = l_Lean_Expr_isConst(v_x_2878_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec_ref(v_x_2879_);
lean_dec_ref(v_x_2878_);
lean_dec_ref(v_e_2874_);
v___x_2893_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
return v___x_2894_;
}
else
{
lean_object* v___x_2895_; lean_object* v___f_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2895_ = l_Lean_Expr_constName_x21(v_x_2878_);
lean_dec_ref(v_x_2878_);
v___f_2896_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2896_, 0, v___x_2895_);
v___x_2897_ = lean_unsigned_to_nat(0u);
v___x_2898_ = l_Array_findIdx_x3f_loop___redArg(v___f_2896_, v_preDefs_2871_, v___x_2897_);
if (lean_obj_tag(v___x_2898_) == 1)
{
lean_object* v_val_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_val_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_val_2899_);
lean_dec_ref(v___x_2898_);
v___x_2900_ = lean_box(0);
v___x_2901_ = lean_array_get_borrowed(v___x_2897_, v___x_2872_, v_val_2899_);
v___x_2902_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2873_, v_val_2899_, v___x_2901_, v_x_2879_, v_e_2874_, v_next_2875_, v_params_2876_, v___x_2877_, v___x_2892_, v___x_2897_, v___x_2900_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec_ref(v_x_2879_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2910_; 
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; 
v_unused_2911_ = lean_ctor_get(v___x_2902_, 0);
lean_dec(v_unused_2911_);
v___x_2904_ = v___x_2902_;
v_isShared_2905_ = v_isSharedCheck_2910_;
goto v_resetjp_2903_;
}
else
{
lean_dec(v___x_2902_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2910_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2906_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 0, v___x_2906_);
v___x_2908_ = v___x_2904_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
v_a_2912_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2902_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2902_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
lean_dec(v___x_2898_);
lean_dec_ref(v_x_2879_);
lean_dec_ref(v_e_2874_);
v___x_2920_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
return v___x_2921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2922_, lean_object* v___x_2923_, lean_object* v_val_2924_, lean_object* v_e_2925_, lean_object* v_next_2926_, lean_object* v_params_2927_, lean_object* v___x_2928_, lean_object* v_x_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2922_, v___x_2923_, v_val_2924_, v_e_2925_, v_next_2926_, v_params_2927_, v___x_2928_, v_x_2929_, v_x_2930_, v_x_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___x_2928_);
lean_dec_ref(v_params_2927_);
lean_dec(v_next_2926_);
lean_dec(v_val_2924_);
lean_dec_ref(v___x_2923_);
lean_dec_ref(v_preDefs_2922_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2938_, lean_object* v___x_2939_, lean_object* v_val_2940_, lean_object* v_a_2941_, lean_object* v_params_2942_, lean_object* v___x_2943_, lean_object* v_e_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_dummy_2950_; lean_object* v_nargs_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_dummy_2950_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2951_ = l_Lean_Expr_getAppNumArgs(v_e_2944_);
lean_inc(v_nargs_2951_);
v___x_2952_ = lean_mk_array(v_nargs_2951_, v_dummy_2950_);
v___x_2953_ = lean_unsigned_to_nat(1u);
v___x_2954_ = lean_nat_sub(v_nargs_2951_, v___x_2953_);
lean_dec(v_nargs_2951_);
lean_inc_ref(v_e_2944_);
v___x_2955_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2938_, v___x_2939_, v_val_2940_, v_e_2944_, v_a_2941_, v_params_2942_, v___x_2943_, v_e_2944_, v___x_2952_, v___x_2954_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2956_, lean_object* v___x_2957_, lean_object* v_val_2958_, lean_object* v_a_2959_, lean_object* v_params_2960_, lean_object* v___x_2961_, lean_object* v_e_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2956_, v___x_2957_, v_val_2958_, v_a_2959_, v_params_2960_, v___x_2961_, v_e_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___x_2961_);
lean_dec_ref(v_params_2960_);
lean_dec(v_a_2959_);
lean_dec(v_val_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_preDefs_2956_);
return v_res_2968_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2972_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2973_ = lean_unsigned_to_nat(6u);
v___x_2974_ = lean_unsigned_to_nat(201u);
v___x_2975_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2976_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2977_ = l_mkPanicMessageWithDecl(v___x_2976_, v___x_2975_, v___x_2974_, v___x_2973_, v___x_2972_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2978_, lean_object* v___x_2979_, lean_object* v_a_2980_, lean_object* v_preDefs_2981_, lean_object* v_val_2982_, lean_object* v___f_2983_, lean_object* v___x_2984_, lean_object* v_params_2985_, lean_object* v_body_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v___x_2992_ = lean_array_get_size(v_params_2985_);
v___x_2993_ = lean_array_get_borrowed(v___x_2978_, v___x_2979_, v_a_2980_);
v___x_2994_ = lean_nat_dec_eq(v___x_2992_, v___x_2993_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_dec_ref(v_body_2986_);
lean_dec_ref(v_params_2985_);
lean_dec_ref(v___f_2983_);
lean_dec(v_val_2982_);
lean_dec_ref(v_preDefs_2981_);
lean_dec(v_a_2980_);
lean_dec_ref(v___x_2979_);
v___x_2995_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2996_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2995_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_2996_;
}
else
{
lean_object* v___f_2997_; uint8_t v___x_2998_; lean_object* v___x_2999_; 
v___f_2997_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_2997_, 0, v_preDefs_2981_);
lean_closure_set(v___f_2997_, 1, v___x_2979_);
lean_closure_set(v___f_2997_, 2, v_val_2982_);
lean_closure_set(v___f_2997_, 3, v_a_2980_);
lean_closure_set(v___f_2997_, 4, v_params_2985_);
lean_closure_set(v___f_2997_, 5, v___x_2992_);
v___x_2998_ = 0;
v___x_2999_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2986_, v___f_2997_, v___f_2983_, v___x_2998_, v___x_2994_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3006_ == 0)
{
lean_object* v_unused_3007_; 
v_unused_3007_ = lean_ctor_get(v___x_2999_, 0);
lean_dec(v_unused_3007_);
v___x_3001_ = v___x_2999_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_dec(v___x_2999_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_2984_);
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2984_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
v_a_3008_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2999_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2999_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_3016_, lean_object* v___x_3017_, lean_object* v_a_3018_, lean_object* v_preDefs_3019_, lean_object* v_val_3020_, lean_object* v___f_3021_, lean_object* v___x_3022_, lean_object* v_params_3023_, lean_object* v_body_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_3016_, v___x_3017_, v_a_3018_, v_preDefs_3019_, v_val_3020_, v___f_3021_, v___x_3022_, v_params_3023_, v_body_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3037_, 0, v_e_3031_);
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v_preDefs_3047_, lean_object* v___x_3048_, lean_object* v_val_3049_, lean_object* v_upperBound_3050_, lean_object* v_a_3051_, lean_object* v_b_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_nat_dec_lt(v_a_3051_, v_upperBound_3050_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; 
lean_dec(v_a_3051_);
lean_dec(v_val_3049_);
lean_dec_ref(v___x_3048_);
lean_dec_ref(v_preDefs_3047_);
v___x_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3059_, 0, v_b_3052_);
return v___x_3059_;
}
else
{
lean_object* v___x_3060_; lean_object* v_value_3061_; lean_object* v___f_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___f_3065_; uint8_t v___x_3066_; lean_object* v___x_3067_; 
v___x_3060_ = lean_array_fget_borrowed(v_preDefs_3047_, v_a_3051_);
v_value_3061_ = lean_ctor_get(v___x_3060_, 7);
v___f_3062_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3063_ = lean_unsigned_to_nat(0u);
v___x_3064_ = lean_box(0);
lean_inc(v_val_3049_);
lean_inc_ref(v_preDefs_3047_);
lean_inc(v_a_3051_);
lean_inc_ref(v___x_3048_);
v___f_3065_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3065_, 0, v___x_3063_);
lean_closure_set(v___f_3065_, 1, v___x_3048_);
lean_closure_set(v___f_3065_, 2, v_a_3051_);
lean_closure_set(v___f_3065_, 3, v_preDefs_3047_);
lean_closure_set(v___f_3065_, 4, v_val_3049_);
lean_closure_set(v___f_3065_, 5, v___f_3062_);
lean_closure_set(v___f_3065_, 6, v___x_3064_);
v___x_3066_ = 0;
lean_inc_ref(v_value_3061_);
v___x_3067_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_3061_, v___f_3065_, v___x_3066_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
lean_dec_ref(v___x_3067_);
v___x_3068_ = lean_unsigned_to_nat(1u);
v___x_3069_ = lean_nat_add(v_a_3051_, v___x_3068_);
lean_dec(v_a_3051_);
v_a_3051_ = v___x_3069_;
v_b_3052_ = v___x_3064_;
goto _start;
}
else
{
lean_dec(v_a_3051_);
lean_dec(v_val_3049_);
lean_dec_ref(v___x_3048_);
lean_dec_ref(v_preDefs_3047_);
return v___x_3067_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v_preDefs_3071_, lean_object* v___x_3072_, lean_object* v_val_3073_, lean_object* v_upperBound_3074_, lean_object* v_a_3075_, lean_object* v_b_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3071_, v___x_3072_, v_val_3073_, v_upperBound_3074_, v_a_3075_, v_b_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v_upperBound_3074_);
return v_res_3082_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3085_ = l_Lean_stringToMessageData(v___x_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
size_t v_sz_3092_; size_t v___x_3093_; lean_object* v___x_3094_; 
v_sz_3092_ = lean_array_size(v_preDefs_3086_);
v___x_3093_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3086_);
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3092_, v___x_3093_, v_preDefs_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; size_t v_sz_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3095_);
lean_dec_ref(v___x_3094_);
v_sz_3096_ = lean_array_size(v_a_3095_);
lean_inc(v_a_3095_);
v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3096_, v___x_3093_, v_a_3095_);
v___x_3098_ = l_Lean_Elab_FixedParams_Info_init(v_a_3095_);
v___x_3099_ = lean_st_mk_ref(v___x_3098_);
v___x_3100_ = lean_st_ref_take(v___x_3099_);
v___x_3101_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3100_);
v___x_3102_ = lean_st_ref_set(v___x_3099_, v___x_3101_);
v___x_3103_ = lean_array_get_size(v_preDefs_3086_);
v___x_3104_ = lean_unsigned_to_nat(0u);
v___x_3105_ = lean_box(0);
lean_inc(v___x_3099_);
v___x_3106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3086_, v___x_3097_, v___x_3099_, v___x_3103_, v___x_3104_, v___x_3105_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3140_; 
lean_dec_ref(v___x_3106_);
v___x_3107_ = lean_st_ref_get(v___x_3099_);
lean_dec(v___x_3099_);
v___x_3108_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3109_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_getFixedParamsInfo_spec__2___redArg(v___x_3108_, v_a_3089_);
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3140_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3140_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
uint8_t v___x_3114_; 
v___x_3114_ = lean_unbox(v_a_3110_);
lean_dec(v_a_3110_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3116_; 
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3107_);
v___x_3116_ = v___x_3112_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3107_);
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
lean_del_object(v___x_3112_);
v___x_3118_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3107_);
v___x_3119_ = l_Lean_Elab_FixedParams_Info_format(v___x_3107_);
v___x_3120_ = l_Std_Format_indentD(v___x_3119_);
v___x_3121_ = l_Lean_MessageData_ofFormat(v___x_3120_);
v___x_3122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3118_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
v___x_3123_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_3108_, v___x_3122_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
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
lean_ctor_set(v___x_3125_, 0, v___x_3107_);
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3107_);
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
lean_dec(v___x_3107_);
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
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec(v___x_3099_);
v_a_3141_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3106_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3106_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec_ref(v_preDefs_3086_);
v_a_3149_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3094_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3094_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_upperBound_3164_, lean_object* v_val_3165_, lean_object* v_next_3166_, lean_object* v_params_3167_, lean_object* v___x_3168_, lean_object* v_val_3169_, lean_object* v_next_3170_, uint8_t v___x_3171_, lean_object* v_inst_3172_, lean_object* v_R_3173_, lean_object* v_a_3174_, uint8_t v_b_3175_, lean_object* v_c_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_3164_, v_val_3165_, v_next_3166_, v_params_3167_, v___x_3168_, v_val_3169_, v_next_3170_, v___x_3171_, v_a_3174_, v_b_3175_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3183_ = _args[0];
lean_object* v_val_3184_ = _args[1];
lean_object* v_next_3185_ = _args[2];
lean_object* v_params_3186_ = _args[3];
lean_object* v___x_3187_ = _args[4];
lean_object* v_val_3188_ = _args[5];
lean_object* v_next_3189_ = _args[6];
lean_object* v___x_3190_ = _args[7];
lean_object* v_inst_3191_ = _args[8];
lean_object* v_R_3192_ = _args[9];
lean_object* v_a_3193_ = _args[10];
lean_object* v_b_3194_ = _args[11];
lean_object* v_c_3195_ = _args[12];
lean_object* v___y_3196_ = _args[13];
lean_object* v___y_3197_ = _args[14];
lean_object* v___y_3198_ = _args[15];
lean_object* v___y_3199_ = _args[16];
lean_object* v___y_3200_ = _args[17];
_start:
{
uint8_t v___x_42620__boxed_3201_; uint8_t v_b_boxed_3202_; lean_object* v_res_3203_; 
v___x_42620__boxed_3201_ = lean_unbox(v___x_3190_);
v_b_boxed_3202_ = lean_unbox(v_b_3194_);
v_res_3203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_upperBound_3183_, v_val_3184_, v_next_3185_, v_params_3186_, v___x_3187_, v_val_3188_, v_next_3189_, v___x_42620__boxed_3201_, v_inst_3191_, v_R_3192_, v_a_3193_, v_b_boxed_3202_, v_c_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v_val_3188_);
lean_dec_ref(v_params_3186_);
lean_dec(v_next_3185_);
lean_dec(v_val_3184_);
lean_dec(v_upperBound_3183_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3204_, lean_object* v_val_3205_, lean_object* v_upperBound_3206_, lean_object* v_args_3207_, lean_object* v_e_3208_, lean_object* v_next_3209_, lean_object* v_params_3210_, lean_object* v___x_3211_, uint8_t v___x_3212_, lean_object* v_inst_3213_, lean_object* v_R_3214_, lean_object* v_a_3215_, lean_object* v_b_3216_, lean_object* v_c_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3204_, v_val_3205_, v_upperBound_3206_, v_args_3207_, v_e_3208_, v_next_3209_, v_params_3210_, v___x_3211_, v___x_3212_, v_a_3215_, v_b_3216_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3224_ = _args[0];
lean_object* v_val_3225_ = _args[1];
lean_object* v_upperBound_3226_ = _args[2];
lean_object* v_args_3227_ = _args[3];
lean_object* v_e_3228_ = _args[4];
lean_object* v_next_3229_ = _args[5];
lean_object* v_params_3230_ = _args[6];
lean_object* v___x_3231_ = _args[7];
lean_object* v___x_3232_ = _args[8];
lean_object* v_inst_3233_ = _args[9];
lean_object* v_R_3234_ = _args[10];
lean_object* v_a_3235_ = _args[11];
lean_object* v_b_3236_ = _args[12];
lean_object* v_c_3237_ = _args[13];
lean_object* v___y_3238_ = _args[14];
lean_object* v___y_3239_ = _args[15];
lean_object* v___y_3240_ = _args[16];
lean_object* v___y_3241_ = _args[17];
lean_object* v___y_3242_ = _args[18];
_start:
{
uint8_t v___x_42655__boxed_3243_; lean_object* v_res_3244_; 
v___x_42655__boxed_3243_ = lean_unbox(v___x_3232_);
v_res_3244_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3224_, v_val_3225_, v_upperBound_3226_, v_args_3227_, v_e_3228_, v_next_3229_, v_params_3230_, v___x_3231_, v___x_42655__boxed_3243_, v_inst_3233_, v_R_3234_, v_a_3235_, v_b_3236_, v_c_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___x_3231_);
lean_dec_ref(v_params_3230_);
lean_dec(v_next_3229_);
lean_dec_ref(v_args_3227_);
lean_dec(v_upperBound_3226_);
lean_dec(v_val_3224_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v_preDefs_3245_, lean_object* v___x_3246_, lean_object* v_val_3247_, lean_object* v_upperBound_3248_, lean_object* v_inst_3249_, lean_object* v_R_3250_, lean_object* v_a_3251_, lean_object* v_b_3252_, lean_object* v_c_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3245_, v___x_3246_, v_val_3247_, v_upperBound_3248_, v_a_3251_, v_b_3252_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v_preDefs_3260_, lean_object* v___x_3261_, lean_object* v_val_3262_, lean_object* v_upperBound_3263_, lean_object* v_inst_3264_, lean_object* v_R_3265_, lean_object* v_a_3266_, lean_object* v_b_3267_, lean_object* v_c_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v_preDefs_3260_, v___x_3261_, v_val_3262_, v_upperBound_3263_, v_inst_3264_, v_R_3265_, v_a_3266_, v_b_3267_, v_c_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v_upperBound_3263_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3275_, lean_object* v___x_3276_, lean_object* v_pre_3277_, lean_object* v_post_3278_, uint8_t v_usedLetOnly_3279_, uint8_t v_skipConstInApp_3280_, uint8_t v_skipInstances_3281_, lean_object* v___x_3282_, lean_object* v_inst_3283_, lean_object* v_R_3284_, lean_object* v_a_3285_, lean_object* v_b_3286_, lean_object* v_c_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3275_, v___x_3276_, v_pre_3277_, v_post_3278_, v_usedLetOnly_3279_, v_skipConstInApp_3280_, v_skipInstances_3281_, v_a_3285_, v_b_3286_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3295_ = _args[0];
lean_object* v___x_3296_ = _args[1];
lean_object* v_pre_3297_ = _args[2];
lean_object* v_post_3298_ = _args[3];
lean_object* v_usedLetOnly_3299_ = _args[4];
lean_object* v_skipConstInApp_3300_ = _args[5];
lean_object* v_skipInstances_3301_ = _args[6];
lean_object* v___x_3302_ = _args[7];
lean_object* v_inst_3303_ = _args[8];
lean_object* v_R_3304_ = _args[9];
lean_object* v_a_3305_ = _args[10];
lean_object* v_b_3306_ = _args[11];
lean_object* v_c_3307_ = _args[12];
lean_object* v___y_3308_ = _args[13];
lean_object* v___y_3309_ = _args[14];
lean_object* v___y_3310_ = _args[15];
lean_object* v___y_3311_ = _args[16];
lean_object* v___y_3312_ = _args[17];
lean_object* v___y_3313_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3314_; uint8_t v_skipConstInApp_boxed_3315_; uint8_t v_skipInstances_boxed_3316_; lean_object* v_res_3317_; 
v_usedLetOnly_boxed_3314_ = lean_unbox(v_usedLetOnly_3299_);
v_skipConstInApp_boxed_3315_ = lean_unbox(v_skipConstInApp_3300_);
v_skipInstances_boxed_3316_ = lean_unbox(v_skipInstances_3301_);
v_res_3317_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3295_, v___x_3296_, v_pre_3297_, v_post_3298_, v_usedLetOnly_boxed_3314_, v_skipConstInApp_boxed_3315_, v_skipInstances_boxed_3316_, v___x_3302_, v_inst_3303_, v_R_3304_, v_a_3305_, v_b_3306_, v_c_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec(v___x_3302_);
lean_dec_ref(v___x_3296_);
lean_dec(v_upperBound_3295_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3318_, lean_object* v_m_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3319_, v_a_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3322_, lean_object* v_m_3323_, lean_object* v_a_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3322_, v_m_3323_, v_a_3324_);
lean_dec_ref(v_a_3324_);
lean_dec_ref(v_m_3323_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3326_, lean_object* v_name_3327_, uint8_t v_bi_3328_, lean_object* v_type_3329_, lean_object* v_k_3330_, uint8_t v_kind_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3327_, v_bi_3328_, v_type_3329_, v_k_3330_, v_kind_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3339_, lean_object* v_name_3340_, lean_object* v_bi_3341_, lean_object* v_type_3342_, lean_object* v_k_3343_, lean_object* v_kind_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
uint8_t v_bi_boxed_3351_; uint8_t v_kind_boxed_3352_; lean_object* v_res_3353_; 
v_bi_boxed_3351_ = lean_unbox(v_bi_3341_);
v_kind_boxed_3352_ = lean_unbox(v_kind_3344_);
v_res_3353_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3339_, v_name_3340_, v_bi_boxed_3351_, v_type_3342_, v_k_3343_, v_kind_boxed_3352_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3354_, lean_object* v_name_3355_, lean_object* v_type_3356_, lean_object* v_val_3357_, lean_object* v_k_3358_, uint8_t v_nondep_3359_, uint8_t v_kind_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3355_, v_type_3356_, v_val_3357_, v_k_3358_, v_nondep_3359_, v_kind_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3368_, lean_object* v_name_3369_, lean_object* v_type_3370_, lean_object* v_val_3371_, lean_object* v_k_3372_, lean_object* v_nondep_3373_, lean_object* v_kind_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
uint8_t v_nondep_boxed_3381_; uint8_t v_kind_boxed_3382_; lean_object* v_res_3383_; 
v_nondep_boxed_3381_ = lean_unbox(v_nondep_3373_);
v_kind_boxed_3382_ = lean_unbox(v_kind_3374_);
v_res_3383_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3368_, v_name_3369_, v_type_3370_, v_val_3371_, v_k_3372_, v_nondep_boxed_3381_, v_kind_boxed_3382_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3384_, lean_object* v_ref_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3385_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3392_, lean_object* v_ref_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3392_, v_ref_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3400_, lean_object* v_x_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___x_3408_; 
lean_inc_ref(v___y_3405_);
v___x_3408_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3409_, lean_object* v_x_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3409_, v_x_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3418_, lean_object* v_m_3419_, lean_object* v_a_3420_, lean_object* v_b_3421_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3419_, v_a_3420_, v_b_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3423_, lean_object* v_a_3424_, lean_object* v_x_3425_){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3424_, v_x_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3427_, lean_object* v_a_3428_, lean_object* v_x_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3427_, v_a_3428_, v_x_3429_);
lean_dec(v_x_3429_);
lean_dec_ref(v_a_3428_);
return v_res_3430_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3431_, lean_object* v_a_3432_, lean_object* v_x_3433_){
_start:
{
uint8_t v___x_3434_; 
v___x_3434_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3432_, v_x_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3435_, lean_object* v_a_3436_, lean_object* v_x_3437_){
_start:
{
uint8_t v_res_3438_; lean_object* v_r_3439_; 
v_res_3438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3435_, v_a_3436_, v_x_3437_);
lean_dec(v_x_3437_);
lean_dec_ref(v_a_3436_);
v_r_3439_ = lean_box(v_res_3438_);
return v_r_3439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3440_, lean_object* v_data_3441_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3441_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3443_, lean_object* v_a_3444_, lean_object* v_b_3445_, lean_object* v_x_3446_){
_start:
{
lean_object* v___x_3447_; 
v___x_3447_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3444_, v_b_3445_, v_x_3446_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3448_, lean_object* v_i_3449_, lean_object* v_source_3450_, lean_object* v_target_3451_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3449_, v_source_3450_, v_target_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3453_, lean_object* v_x_3454_, lean_object* v_x_3455_){
_start:
{
lean_object* v___x_3456_; 
v___x_3456_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3454_, v_x_3455_);
return v___x_3456_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1(void){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3459_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__0));
v___x_3460_ = lean_unsigned_to_nat(0u);
v___x_3461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
lean_ctor_set(v___x_3461_, 1, v___x_3459_);
lean_ctor_set(v___x_3461_, 2, v___x_3459_);
return v___x_3461_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFixedParamPerms_default(void){
_start:
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_obj_once(&l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1, &l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1_once, _init_l_Lean_Elab_instInhabitedFixedParamPerms_default___closed__1);
return v___x_3462_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFixedParamPerms(void){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Lean_Elab_instInhabitedFixedParamPerms_default;
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3470_, lean_object* v_x_3471_){
_start:
{
if (lean_obj_tag(v_x_3470_) == 0)
{
lean_object* v___x_3472_; 
v___x_3472_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3472_;
}
else
{
lean_object* v_val_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3484_; 
v_val_3473_ = lean_ctor_get(v_x_3470_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_x_3470_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3475_ = v_x_3470_;
v_isShared_3476_ = v_isSharedCheck_3484_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_val_3473_);
lean_dec(v_x_3470_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3484_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3480_; 
v___x_3477_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3478_ = l_Nat_reprFast(v_val_3473_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set_tag(v___x_3475_, 3);
lean_ctor_set(v___x_3475_, 0, v___x_3478_);
v___x_3480_ = v___x_3475_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3477_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = l_Repr_addAppParen(v___x_3481_, v_x_3471_);
return v___x_3482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3485_, lean_object* v_x_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3485_, v_x_3486_);
lean_dec(v_x_3486_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3488_, lean_object* v_x_3489_, lean_object* v_x_3490_){
_start:
{
if (lean_obj_tag(v_x_3490_) == 0)
{
lean_dec(v_x_3488_);
return v_x_3489_;
}
else
{
lean_object* v_head_3491_; lean_object* v_tail_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3503_; 
v_head_3491_ = lean_ctor_get(v_x_3490_, 0);
v_tail_3492_ = lean_ctor_get(v_x_3490_, 1);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_x_3490_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3494_ = v_x_3490_;
v_isShared_3495_ = v_isSharedCheck_3503_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_tail_3492_);
lean_inc(v_head_3491_);
lean_dec(v_x_3490_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3503_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
lean_inc(v_x_3488_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set_tag(v___x_3494_, 5);
lean_ctor_set(v___x_3494_, 1, v_x_3488_);
lean_ctor_set(v___x_3494_, 0, v_x_3489_);
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_x_3489_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_x_3488_);
v___x_3497_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = lean_unsigned_to_nat(0u);
v___x_3499_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3491_, v___x_3498_);
v___x_3500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3497_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
v_x_3489_ = v___x_3500_;
v_x_3490_ = v_tail_3492_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3504_, lean_object* v_x_3505_, lean_object* v_x_3506_){
_start:
{
if (lean_obj_tag(v_x_3506_) == 0)
{
lean_dec(v_x_3504_);
return v_x_3505_;
}
else
{
lean_object* v_head_3507_; lean_object* v_tail_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3519_; 
v_head_3507_ = lean_ctor_get(v_x_3506_, 0);
v_tail_3508_ = lean_ctor_get(v_x_3506_, 1);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_x_3506_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3510_ = v_x_3506_;
v_isShared_3511_ = v_isSharedCheck_3519_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_tail_3508_);
lean_inc(v_head_3507_);
lean_dec(v_x_3506_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3519_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
lean_inc(v_x_3504_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set_tag(v___x_3510_, 5);
lean_ctor_set(v___x_3510_, 1, v_x_3504_);
lean_ctor_set(v___x_3510_, 0, v_x_3505_);
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_x_3505_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_x_3504_);
v___x_3513_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3514_ = lean_unsigned_to_nat(0u);
v___x_3515_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3507_, v___x_3514_);
v___x_3516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3513_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
v___x_3517_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3504_, v___x_3516_, v_tail_3508_);
return v___x_3517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = lean_unsigned_to_nat(0u);
v___x_3522_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3520_, v___x_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3523_, lean_object* v_x_3524_){
_start:
{
if (lean_obj_tag(v_x_3523_) == 0)
{
lean_object* v___x_3525_; 
lean_dec(v_x_3524_);
v___x_3525_ = lean_box(0);
return v___x_3525_;
}
else
{
lean_object* v_tail_3526_; 
v_tail_3526_ = lean_ctor_get(v_x_3523_, 1);
if (lean_obj_tag(v_tail_3526_) == 0)
{
lean_object* v_head_3527_; lean_object* v___x_3528_; 
lean_dec(v_x_3524_);
v_head_3527_ = lean_ctor_get(v_x_3523_, 0);
lean_inc(v_head_3527_);
lean_dec_ref(v_x_3523_);
v___x_3528_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3527_);
return v___x_3528_;
}
else
{
lean_object* v_head_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_inc(v_tail_3526_);
v_head_3529_ = lean_ctor_get(v_x_3523_, 0);
lean_inc(v_head_3529_);
lean_dec_ref(v_x_3523_);
v___x_3530_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3529_);
v___x_3531_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3524_, v___x_3530_, v_tail_3526_);
return v___x_3531_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3540_ = lean_string_length(v___x_3539_);
return v___x_3540_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3542_ = lean_nat_to_int(v___x_3541_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3548_){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v___x_3549_ = lean_array_get_size(v_xs_3548_);
v___x_3550_ = lean_unsigned_to_nat(0u);
v___x_3551_ = lean_nat_dec_eq(v___x_3549_, v___x_3550_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3552_ = lean_array_to_list(v_xs_3548_);
v___x_3553_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3554_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3552_, v___x_3553_);
v___x_3555_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3556_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
lean_ctor_set(v___x_3557_, 1, v___x_3554_);
v___x_3558_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3557_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3555_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = l_Std_Format_fill(v___x_3560_);
return v___x_3561_;
}
else
{
lean_object* v___x_3562_; 
lean_dec_ref(v_xs_3548_);
v___x_3562_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3562_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3563_, lean_object* v_x_3564_, lean_object* v_x_3565_){
_start:
{
if (lean_obj_tag(v_x_3565_) == 0)
{
lean_dec(v_x_3563_);
return v_x_3564_;
}
else
{
lean_object* v_head_3566_; lean_object* v_tail_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3577_; 
v_head_3566_ = lean_ctor_get(v_x_3565_, 0);
v_tail_3567_ = lean_ctor_get(v_x_3565_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_x_3565_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3569_ = v_x_3565_;
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_tail_3567_);
lean_inc(v_head_3566_);
lean_dec(v_x_3565_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
lean_inc(v_x_3563_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set_tag(v___x_3569_, 5);
lean_ctor_set(v___x_3569_, 1, v_x_3563_);
lean_ctor_set(v___x_3569_, 0, v_x_3564_);
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_x_3564_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_x_3563_);
v___x_3572_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3566_);
v___x_3574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3572_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v_x_3564_ = v___x_3574_;
v_x_3565_ = v_tail_3567_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3578_, lean_object* v_x_3579_){
_start:
{
if (lean_obj_tag(v_x_3578_) == 0)
{
lean_object* v___x_3580_; 
lean_dec(v_x_3579_);
v___x_3580_ = lean_box(0);
return v___x_3580_;
}
else
{
lean_object* v_tail_3581_; 
v_tail_3581_ = lean_ctor_get(v_x_3578_, 1);
if (lean_obj_tag(v_tail_3581_) == 0)
{
lean_object* v_head_3582_; lean_object* v___x_3583_; 
lean_dec(v_x_3579_);
v_head_3582_ = lean_ctor_get(v_x_3578_, 0);
lean_inc(v_head_3582_);
lean_dec_ref(v_x_3578_);
v___x_3583_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3582_);
return v___x_3583_;
}
else
{
lean_object* v_head_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_inc(v_tail_3581_);
v_head_3584_ = lean_ctor_get(v_x_3578_, 0);
lean_inc(v_head_3584_);
lean_dec_ref(v_x_3578_);
v___x_3585_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3584_);
v___x_3586_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3579_, v___x_3585_, v_tail_3581_);
return v___x_3586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3587_){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; 
v___x_3588_ = lean_array_get_size(v_xs_3587_);
v___x_3589_ = lean_unsigned_to_nat(0u);
v___x_3590_ = lean_nat_dec_eq(v___x_3588_, v___x_3589_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3591_ = lean_array_to_list(v_xs_3587_);
v___x_3592_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3593_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3591_, v___x_3592_);
v___x_3594_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3595_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
lean_ctor_set(v___x_3596_, 1, v___x_3593_);
v___x_3597_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3594_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = l_Std_Format_fill(v___x_3599_);
return v___x_3600_;
}
else
{
lean_object* v___x_3601_; 
lean_dec_ref(v_xs_3587_);
v___x_3601_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3601_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3602_, lean_object* v_x_3603_, lean_object* v_x_3604_){
_start:
{
if (lean_obj_tag(v_x_3604_) == 0)
{
lean_dec(v_x_3602_);
return v_x_3603_;
}
else
{
lean_object* v_head_3605_; lean_object* v_tail_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3617_; 
v_head_3605_ = lean_ctor_get(v_x_3604_, 0);
v_tail_3606_ = lean_ctor_get(v_x_3604_, 1);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_x_3604_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3608_ = v_x_3604_;
v_isShared_3609_ = v_isSharedCheck_3617_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_tail_3606_);
lean_inc(v_head_3605_);
lean_dec(v_x_3604_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3617_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
lean_inc(v_x_3602_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set_tag(v___x_3608_, 5);
lean_ctor_set(v___x_3608_, 1, v_x_3602_);
lean_ctor_set(v___x_3608_, 0, v_x_3603_);
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_x_3603_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_x_3602_);
v___x_3611_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3612_ = l_Nat_reprFast(v_head_3605_);
v___x_3613_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
v___x_3614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3611_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v_x_3603_ = v___x_3614_;
v_x_3604_ = v_tail_3606_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3618_, lean_object* v_x_3619_, lean_object* v_x_3620_){
_start:
{
if (lean_obj_tag(v_x_3620_) == 0)
{
lean_dec(v_x_3618_);
return v_x_3619_;
}
else
{
lean_object* v_head_3621_; lean_object* v_tail_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3633_; 
v_head_3621_ = lean_ctor_get(v_x_3620_, 0);
v_tail_3622_ = lean_ctor_get(v_x_3620_, 1);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_x_3620_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3624_ = v_x_3620_;
v_isShared_3625_ = v_isSharedCheck_3633_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_tail_3622_);
lean_inc(v_head_3621_);
lean_dec(v_x_3620_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3633_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
lean_inc(v_x_3618_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set_tag(v___x_3624_, 5);
lean_ctor_set(v___x_3624_, 1, v_x_3618_);
lean_ctor_set(v___x_3624_, 0, v_x_3619_);
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_x_3619_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v_x_3618_);
v___x_3627_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3628_ = l_Nat_reprFast(v_head_3621_);
v___x_3629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
v___x_3630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3627_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3618_, v___x_3630_, v_tail_3622_);
return v___x_3631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3634_){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = l_Nat_reprFast(v___y_3634_);
v___x_3636_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3637_, lean_object* v_x_3638_){
_start:
{
if (lean_obj_tag(v_x_3637_) == 0)
{
lean_object* v___x_3639_; 
lean_dec(v_x_3638_);
v___x_3639_ = lean_box(0);
return v___x_3639_;
}
else
{
lean_object* v_tail_3640_; 
v_tail_3640_ = lean_ctor_get(v_x_3637_, 1);
if (lean_obj_tag(v_tail_3640_) == 0)
{
lean_object* v_head_3641_; lean_object* v___x_3642_; 
lean_dec(v_x_3638_);
v_head_3641_ = lean_ctor_get(v_x_3637_, 0);
lean_inc(v_head_3641_);
lean_dec_ref(v_x_3637_);
v___x_3642_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3641_);
return v___x_3642_;
}
else
{
lean_object* v_head_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
lean_inc(v_tail_3640_);
v_head_3643_ = lean_ctor_get(v_x_3637_, 0);
lean_inc(v_head_3643_);
lean_dec_ref(v_x_3637_);
v___x_3644_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3643_);
v___x_3645_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3638_, v___x_3644_, v_tail_3640_);
return v___x_3645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3646_){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v___x_3647_ = lean_array_get_size(v_xs_3646_);
v___x_3648_ = lean_unsigned_to_nat(0u);
v___x_3649_ = lean_nat_dec_eq(v___x_3647_, v___x_3648_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3650_ = lean_array_to_list(v_xs_3646_);
v___x_3651_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3652_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3650_, v___x_3651_);
v___x_3653_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3654_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
lean_ctor_set(v___x_3655_, 1, v___x_3652_);
v___x_3656_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3653_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = l_Std_Format_fill(v___x_3658_);
return v___x_3659_;
}
else
{
lean_object* v___x_3660_; 
lean_dec_ref(v_xs_3646_);
v___x_3660_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3660_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3661_, lean_object* v_x_3662_, lean_object* v_x_3663_){
_start:
{
if (lean_obj_tag(v_x_3663_) == 0)
{
lean_dec(v_x_3661_);
return v_x_3662_;
}
else
{
lean_object* v_head_3664_; lean_object* v_tail_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3675_; 
v_head_3664_ = lean_ctor_get(v_x_3663_, 0);
v_tail_3665_ = lean_ctor_get(v_x_3663_, 1);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_x_3663_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3667_ = v_x_3663_;
v_isShared_3668_ = v_isSharedCheck_3675_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_tail_3665_);
lean_inc(v_head_3664_);
lean_dec(v_x_3663_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3675_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
lean_inc(v_x_3661_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set_tag(v___x_3667_, 5);
lean_ctor_set(v___x_3667_, 1, v_x_3661_);
lean_ctor_set(v___x_3667_, 0, v_x_3662_);
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_x_3662_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_x_3661_);
v___x_3670_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3671_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3664_);
v___x_3672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3670_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
v_x_3662_ = v___x_3672_;
v_x_3663_ = v_tail_3665_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3676_, lean_object* v_x_3677_){
_start:
{
if (lean_obj_tag(v_x_3676_) == 0)
{
lean_object* v___x_3678_; 
lean_dec(v_x_3677_);
v___x_3678_ = lean_box(0);
return v___x_3678_;
}
else
{
lean_object* v_tail_3679_; 
v_tail_3679_ = lean_ctor_get(v_x_3676_, 1);
if (lean_obj_tag(v_tail_3679_) == 0)
{
lean_object* v_head_3680_; lean_object* v___x_3681_; 
lean_dec(v_x_3677_);
v_head_3680_ = lean_ctor_get(v_x_3676_, 0);
lean_inc(v_head_3680_);
lean_dec_ref(v_x_3676_);
v___x_3681_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3680_);
return v___x_3681_;
}
else
{
lean_object* v_head_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
lean_inc(v_tail_3679_);
v_head_3682_ = lean_ctor_get(v_x_3676_, 0);
lean_inc(v_head_3682_);
lean_dec_ref(v_x_3676_);
v___x_3683_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3682_);
v___x_3684_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3677_, v___x_3683_, v_tail_3679_);
return v___x_3684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3685_){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
v___x_3686_ = lean_array_get_size(v_xs_3685_);
v___x_3687_ = lean_unsigned_to_nat(0u);
v___x_3688_ = lean_nat_dec_eq(v___x_3686_, v___x_3687_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3689_ = lean_array_to_list(v_xs_3685_);
v___x_3690_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3691_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3689_, v___x_3690_);
v___x_3692_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3693_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
lean_ctor_set(v___x_3694_, 1, v___x_3691_);
v___x_3695_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3692_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = l_Std_Format_fill(v___x_3697_);
return v___x_3698_;
}
else
{
lean_object* v___x_3699_; 
lean_dec_ref(v_xs_3685_);
v___x_3699_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3699_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3700_, lean_object* v_x_3701_, lean_object* v_x_3702_){
_start:
{
if (lean_obj_tag(v_x_3702_) == 0)
{
lean_dec(v_x_3700_);
return v_x_3701_;
}
else
{
lean_object* v_head_3703_; lean_object* v_tail_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3714_; 
v_head_3703_ = lean_ctor_get(v_x_3702_, 0);
v_tail_3704_ = lean_ctor_get(v_x_3702_, 1);
v_isSharedCheck_3714_ = !lean_is_exclusive(v_x_3702_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3706_ = v_x_3702_;
v_isShared_3707_ = v_isSharedCheck_3714_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_tail_3704_);
lean_inc(v_head_3703_);
lean_dec(v_x_3702_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3714_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
lean_inc(v_x_3700_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set_tag(v___x_3706_, 5);
lean_ctor_set(v___x_3706_, 1, v_x_3700_);
lean_ctor_set(v___x_3706_, 0, v_x_3701_);
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_x_3701_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_x_3700_);
v___x_3709_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3703_);
v___x_3711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v_x_3701_ = v___x_3711_;
v_x_3702_ = v_tail_3704_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3715_, lean_object* v_x_3716_){
_start:
{
if (lean_obj_tag(v_x_3715_) == 0)
{
lean_object* v___x_3717_; 
lean_dec(v_x_3716_);
v___x_3717_ = lean_box(0);
return v___x_3717_;
}
else
{
lean_object* v_tail_3718_; 
v_tail_3718_ = lean_ctor_get(v_x_3715_, 1);
if (lean_obj_tag(v_tail_3718_) == 0)
{
lean_object* v_head_3719_; lean_object* v___x_3720_; 
lean_dec(v_x_3716_);
v_head_3719_ = lean_ctor_get(v_x_3715_, 0);
lean_inc(v_head_3719_);
lean_dec_ref(v_x_3715_);
v___x_3720_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3719_);
return v___x_3720_;
}
else
{
lean_object* v_head_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
lean_inc(v_tail_3718_);
v_head_3721_ = lean_ctor_get(v_x_3715_, 0);
lean_inc(v_head_3721_);
lean_dec_ref(v_x_3715_);
v___x_3722_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3721_);
v___x_3723_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3716_, v___x_3722_, v_tail_3718_);
return v___x_3723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3724_){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; 
v___x_3725_ = lean_array_get_size(v_xs_3724_);
v___x_3726_ = lean_unsigned_to_nat(0u);
v___x_3727_ = lean_nat_dec_eq(v___x_3725_, v___x_3726_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3728_ = lean_array_to_list(v_xs_3724_);
v___x_3729_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3730_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3728_, v___x_3729_);
v___x_3731_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3732_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
lean_ctor_set(v___x_3733_, 1, v___x_3730_);
v___x_3734_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3731_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = l_Std_Format_fill(v___x_3736_);
return v___x_3737_;
}
else
{
lean_object* v___x_3738_; 
lean_dec_ref(v_xs_3724_);
v___x_3738_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3738_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_unsigned_to_nat(12u);
v___x_3753_ = lean_nat_to_int(v___x_3752_);
return v___x_3753_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3757_ = lean_unsigned_to_nat(9u);
v___x_3758_ = lean_nat_to_int(v___x_3757_);
return v___x_3758_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = lean_unsigned_to_nat(11u);
v___x_3763_ = lean_nat_to_int(v___x_3762_);
return v___x_3763_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3765_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3766_ = lean_string_length(v___x_3765_);
return v___x_3766_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3767_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3768_ = lean_nat_to_int(v___x_3767_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3773_){
_start:
{
lean_object* v_numFixed_3774_; lean_object* v_perms_3775_; lean_object* v_revDeps_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v_numFixed_3774_ = lean_ctor_get(v_x_3773_, 0);
lean_inc(v_numFixed_3774_);
v_perms_3775_ = lean_ctor_get(v_x_3773_, 1);
lean_inc_ref(v_perms_3775_);
v_revDeps_3776_ = lean_ctor_get(v_x_3773_, 2);
lean_inc_ref(v_revDeps_3776_);
lean_dec_ref(v_x_3773_);
v___x_3777_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3778_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3779_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3780_ = l_Nat_reprFast(v_numFixed_3774_);
v___x_3781_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
v___x_3782_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3779_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = 0;
v___x_3784_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set_uint8(v___x_3784_, sizeof(void*)*1, v___x_3783_);
v___x_3785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3778_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3785_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = lean_box(1);
v___x_3789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3789_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
lean_ctor_set(v___x_3792_, 1, v___x_3777_);
v___x_3793_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3794_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3775_);
v___x_3795_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3793_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
lean_ctor_set_uint8(v___x_3796_, sizeof(void*)*1, v___x_3783_);
v___x_3797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3792_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
lean_ctor_set(v___x_3798_, 1, v___x_3786_);
v___x_3799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
lean_ctor_set(v___x_3799_, 1, v___x_3788_);
v___x_3800_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3799_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
lean_ctor_set(v___x_3802_, 1, v___x_3777_);
v___x_3803_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3804_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3776_);
v___x_3805_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3803_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
v___x_3806_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set_uint8(v___x_3806_, sizeof(void*)*1, v___x_3783_);
v___x_3807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3802_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3809_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
lean_ctor_set(v___x_3810_, 1, v___x_3807_);
v___x_3811_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3808_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set_uint8(v___x_3814_, sizeof(void*)*1, v___x_3783_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3815_, lean_object* v_prec_3816_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3815_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3818_, lean_object* v_prec_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3818_, v_prec_3819_);
lean_dec(v_prec_3819_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___f_3829_; lean_object* v___x_5797__overap_3830_; lean_object* v___x_3831_; 
v___f_3829_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5797__overap_3830_ = lean_panic_fn(v___f_3829_, v_msg_3823_);
lean_inc(v___y_3827_);
lean_inc_ref(v___y_3826_);
lean_inc(v___y_3825_);
lean_inc_ref(v___y_3824_);
v___x_3831_ = lean_apply_5(v___x_5797__overap_3830_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, lean_box(0));
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___f_3845_; lean_object* v___x_5807__overap_3846_; lean_object* v___x_3847_; 
v___f_3845_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5807__overap_3846_ = lean_panic_fn(v___f_3845_, v_msg_3839_);
lean_inc(v___y_3843_);
lean_inc_ref(v___y_3842_);
lean_inc(v___y_3841_);
lean_inc_ref(v___y_3840_);
v___x_3847_ = lean_apply_5(v___x_5807__overap_3846_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, lean_box(0));
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v___f_3861_; lean_object* v___x_5817__overap_3862_; lean_object* v___x_3863_; 
v___f_3861_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5817__overap_3862_ = lean_panic_fn(v___f_3861_, v_msg_3855_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
lean_inc(v___y_3857_);
lean_inc_ref(v___y_3856_);
v___x_3863_ = lean_apply_5(v___x_5817__overap_3862_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, lean_box(0));
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
return v_res_3870_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3874_ = lean_unsigned_to_nat(12u);
v___x_3875_ = lean_unsigned_to_nat(294u);
v___x_3876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3877_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3878_ = l_mkPanicMessageWithDecl(v___x_3877_, v___x_3876_, v___x_3875_, v___x_3874_, v___x_3873_);
return v___x_3878_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3881_ = lean_unsigned_to_nat(12u);
v___x_3882_ = lean_unsigned_to_nat(297u);
v___x_3883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3884_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3885_ = l_mkPanicMessageWithDecl(v___x_3884_, v___x_3883_, v___x_3882_, v___x_3881_, v___x_3880_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3886_, lean_object* v_as_3887_, size_t v_sz_3888_, size_t v_i_3889_, lean_object* v_b_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v_a_3897_; uint8_t v___x_3901_; 
v___x_3901_ = lean_usize_dec_lt(v_i_3889_, v_sz_3888_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; 
v___x_3902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3902_, 0, v_b_3890_);
return v___x_3902_;
}
else
{
lean_object* v_a_3903_; 
v_a_3903_ = lean_array_uget_borrowed(v_as_3887_, v_i_3889_);
if (lean_obj_tag(v_a_3903_) == 1)
{
lean_object* v_val_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_val_3904_ = lean_ctor_get(v_a_3903_, 0);
v___x_3905_ = lean_unsigned_to_nat(0u);
v___x_3906_ = lean_box(0);
v___x_3907_ = lean_array_get_borrowed(v___x_3906_, v_val_3904_, v___x_3905_);
if (lean_obj_tag(v___x_3907_) == 1)
{
lean_object* v_val_3908_; lean_object* v___x_3909_; 
v_val_3908_ = lean_ctor_get(v___x_3907_, 0);
v___x_3909_ = lean_array_get_borrowed(v___x_3906_, v___x_3886_, v_val_3908_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_dec_ref(v_b_3890_);
v___x_3910_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3911_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3910_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3921_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3914_ = v___x_3911_;
v_isShared_3915_ = v_isSharedCheck_3921_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3911_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3921_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
if (lean_obj_tag(v_a_3912_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3918_; 
v_a_3916_ = lean_ctor_get(v_a_3912_, 0);
lean_inc(v_a_3916_);
lean_dec_ref(v_a_3912_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v_a_3916_);
v___x_3918_ = v___x_3914_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
else
{
lean_object* v_a_3920_; 
lean_del_object(v___x_3914_);
v_a_3920_ = lean_ctor_get(v_a_3912_, 0);
lean_inc(v_a_3920_);
lean_dec_ref(v_a_3912_);
v_a_3897_ = v_a_3920_;
goto v___jp_3896_;
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
v_a_3922_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3911_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3911_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
lean_object* v___x_3930_; 
lean_inc_ref(v___x_3909_);
v___x_3930_ = lean_array_push(v_b_3890_, v___x_3909_);
v_a_3897_ = v___x_3930_;
goto v___jp_3896_;
}
}
else
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3931_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3932_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3931_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_dec_ref(v___x_3932_);
v_a_3897_ = v_b_3890_;
goto v___jp_3896_;
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec_ref(v_b_3890_);
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3932_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3932_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = lean_box(0);
v___x_3942_ = lean_array_push(v_b_3890_, v___x_3941_);
v_a_3897_ = v___x_3942_;
goto v___jp_3896_;
}
}
v___jp_3896_:
{
size_t v___x_3898_; size_t v___x_3899_; 
v___x_3898_ = ((size_t)1ULL);
v___x_3899_ = lean_usize_add(v_i_3889_, v___x_3898_);
v_i_3889_ = v___x_3899_;
v_b_3890_ = v_a_3897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3943_, lean_object* v_as_3944_, lean_object* v_sz_3945_, lean_object* v_i_3946_, lean_object* v_b_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
size_t v_sz_boxed_3953_; size_t v_i_boxed_3954_; lean_object* v_res_3955_; 
v_sz_boxed_3953_ = lean_unbox_usize(v_sz_3945_);
lean_dec(v_sz_3945_);
v_i_boxed_3954_ = lean_unbox_usize(v_i_3946_);
lean_dec(v_i_3946_);
v_res_3955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3943_, v_as_3944_, v_sz_boxed_3953_, v_i_boxed_3954_, v_b_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec_ref(v_as_3944_);
lean_dec_ref(v___x_3943_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3958_, lean_object* v___x_3959_, lean_object* v___x_3960_, lean_object* v_a_3961_, lean_object* v_b_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
uint8_t v___x_3968_; 
v___x_3968_ = lean_nat_dec_lt(v_a_3961_, v_upperBound_3958_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; 
lean_dec(v_a_3961_);
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v_b_3962_);
return v___x_3969_;
}
else
{
lean_object* v___x_3970_; lean_object* v___x_3971_; size_t v_sz_3972_; size_t v___x_3973_; lean_object* v___x_3974_; 
v___x_3970_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3971_ = lean_array_fget_borrowed(v___x_3959_, v_a_3961_);
v_sz_3972_ = lean_array_size(v___x_3971_);
v___x_3973_ = ((size_t)0ULL);
v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3960_, v___x_3971_, v_sz_3972_, v___x_3973_, v___x_3970_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_a_3975_);
lean_dec_ref(v___x_3974_);
v___x_3976_ = lean_array_push(v_b_3962_, v_a_3975_);
v___x_3977_ = lean_unsigned_to_nat(1u);
v___x_3978_ = lean_nat_add(v_a_3961_, v___x_3977_);
lean_dec(v_a_3961_);
v_a_3961_ = v___x_3978_;
v_b_3962_ = v___x_3976_;
goto _start;
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec_ref(v_b_3962_);
lean_dec(v_a_3961_);
v_a_3980_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3974_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3974_);
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
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3988_, lean_object* v___x_3989_, lean_object* v___x_3990_, lean_object* v_a_3991_, lean_object* v_b_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3988_, v___x_3989_, v___x_3990_, v_a_3991_, v_b_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec_ref(v___x_3990_);
lean_dec_ref(v___x_3989_);
lean_dec(v_upperBound_3988_);
return v_res_3998_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4000_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_4001_ = lean_unsigned_to_nat(8u);
v___x_4002_ = lean_unsigned_to_nat(281u);
v___x_4003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4004_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4005_ = l_mkPanicMessageWithDecl(v___x_4004_, v___x_4003_, v___x_4002_, v___x_4001_, v___x_4000_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_4006_, lean_object* v_a_4007_, lean_object* v_b_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_a_4015_; uint8_t v___x_4019_; 
v___x_4019_ = lean_nat_dec_lt(v_a_4007_, v_upperBound_4006_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4020_; 
lean_dec(v_a_4007_);
v___x_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4020_, 0, v_b_4008_);
return v___x_4020_;
}
else
{
lean_object* v_snd_4021_; lean_object* v_snd_4022_; lean_object* v_snd_4023_; lean_object* v_fst_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4148_; 
v_snd_4021_ = lean_ctor_get(v_b_4008_, 1);
lean_inc(v_snd_4021_);
v_snd_4022_ = lean_ctor_get(v_snd_4021_, 1);
lean_inc(v_snd_4022_);
v_snd_4023_ = lean_ctor_get(v_snd_4022_, 1);
lean_inc(v_snd_4023_);
v_fst_4024_ = lean_ctor_get(v_b_4008_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_b_4008_);
if (v_isSharedCheck_4148_ == 0)
{
lean_object* v_unused_4149_; 
v_unused_4149_ = lean_ctor_get(v_b_4008_, 1);
lean_dec(v_unused_4149_);
v___x_4026_ = v_b_4008_;
v_isShared_4027_ = v_isSharedCheck_4148_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_fst_4024_);
lean_dec(v_b_4008_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4148_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v_fst_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4146_; 
v_fst_4028_ = lean_ctor_get(v_snd_4021_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_snd_4021_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; 
v_unused_4147_ = lean_ctor_get(v_snd_4021_, 1);
lean_dec(v_unused_4147_);
v___x_4030_ = v_snd_4021_;
v_isShared_4031_ = v_isSharedCheck_4146_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_fst_4028_);
lean_dec(v_snd_4021_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4146_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v_fst_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4144_; 
v_fst_4032_ = lean_ctor_get(v_snd_4022_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_snd_4022_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; 
v_unused_4145_ = lean_ctor_get(v_snd_4022_, 1);
lean_dec(v_unused_4145_);
v___x_4034_ = v_snd_4022_;
v_isShared_4035_ = v_isSharedCheck_4144_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_fst_4032_);
lean_dec(v_snd_4022_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4144_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v_array_4036_; lean_object* v_start_4037_; lean_object* v_stop_4038_; uint8_t v___x_4039_; 
v_array_4036_ = lean_ctor_get(v_snd_4023_, 0);
v_start_4037_ = lean_ctor_get(v_snd_4023_, 1);
v_stop_4038_ = lean_ctor_get(v_snd_4023_, 2);
v___x_4039_ = lean_nat_dec_lt(v_start_4037_, v_stop_4038_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4041_; 
lean_dec(v_a_4007_);
if (v_isShared_4035_ == 0)
{
v___x_4041_ = v___x_4034_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_fst_4032_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_snd_4023_);
v___x_4041_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4043_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v___x_4041_);
v___x_4043_ = v___x_4030_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_fst_4028_);
lean_ctor_set(v_reuseFailAlloc_4048_, 1, v___x_4041_);
v___x_4043_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
lean_object* v___x_4045_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4043_);
v___x_4045_ = v___x_4026_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_fst_4024_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v___x_4043_);
v___x_4045_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
lean_object* v___x_4046_; 
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
}
}
}
else
{
lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4140_; 
lean_inc(v_stop_4038_);
lean_inc(v_start_4037_);
lean_inc_ref(v_array_4036_);
v_isSharedCheck_4140_ = !lean_is_exclusive(v_snd_4023_);
if (v_isSharedCheck_4140_ == 0)
{
lean_object* v_unused_4141_; lean_object* v_unused_4142_; lean_object* v_unused_4143_; 
v_unused_4141_ = lean_ctor_get(v_snd_4023_, 2);
lean_dec(v_unused_4141_);
v_unused_4142_ = lean_ctor_get(v_snd_4023_, 1);
lean_dec(v_unused_4142_);
v_unused_4143_ = lean_ctor_get(v_snd_4023_, 0);
lean_dec(v_unused_4143_);
v___x_4051_ = v_snd_4023_;
v_isShared_4052_ = v_isSharedCheck_4140_;
goto v_resetjp_4050_;
}
else
{
lean_dec(v_snd_4023_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4140_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v_array_4053_; lean_object* v_start_4054_; lean_object* v_stop_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4060_; 
v_array_4053_ = lean_ctor_get(v_fst_4032_, 0);
v_start_4054_ = lean_ctor_get(v_fst_4032_, 1);
v_stop_4055_ = lean_ctor_get(v_fst_4032_, 2);
v___x_4056_ = lean_array_fget(v_array_4036_, v_start_4037_);
v___x_4057_ = lean_unsigned_to_nat(1u);
v___x_4058_ = lean_nat_add(v_start_4037_, v___x_4057_);
lean_dec(v_start_4037_);
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 1, v___x_4058_);
v___x_4060_ = v___x_4051_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_array_4036_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v___x_4058_);
lean_ctor_set(v_reuseFailAlloc_4139_, 2, v_stop_4038_);
v___x_4060_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
uint8_t v___x_4061_; 
v___x_4061_ = lean_nat_dec_lt(v_start_4054_, v_stop_4055_);
if (v___x_4061_ == 0)
{
lean_object* v___x_4063_; 
lean_dec(v___x_4056_);
lean_dec(v_a_4007_);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 1, v___x_4060_);
v___x_4063_ = v___x_4034_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_fst_4032_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v___x_4060_);
v___x_4063_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4065_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v___x_4063_);
v___x_4065_ = v___x_4030_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_fst_4028_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
lean_object* v___x_4067_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4065_);
v___x_4067_ = v___x_4026_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_fst_4024_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v___x_4065_);
v___x_4067_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
lean_object* v___x_4068_; 
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
return v___x_4068_;
}
}
}
}
else
{
lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4135_; 
lean_inc(v_stop_4055_);
lean_inc(v_start_4054_);
lean_inc_ref(v_array_4053_);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_fst_4032_);
if (v_isSharedCheck_4135_ == 0)
{
lean_object* v_unused_4136_; lean_object* v_unused_4137_; lean_object* v_unused_4138_; 
v_unused_4136_ = lean_ctor_get(v_fst_4032_, 2);
lean_dec(v_unused_4136_);
v_unused_4137_ = lean_ctor_get(v_fst_4032_, 1);
lean_dec(v_unused_4137_);
v_unused_4138_ = lean_ctor_get(v_fst_4032_, 0);
lean_dec(v_unused_4138_);
v___x_4073_ = v_fst_4032_;
v_isShared_4074_ = v_isSharedCheck_4135_;
goto v_resetjp_4072_;
}
else
{
lean_dec(v_fst_4032_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4135_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4075_; lean_object* v___x_4077_; 
v___x_4075_ = lean_nat_add(v_start_4054_, v___x_4057_);
lean_dec(v_start_4054_);
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 1, v___x_4075_);
v___x_4077_ = v___x_4073_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_array_4053_);
lean_ctor_set(v_reuseFailAlloc_4134_, 1, v___x_4075_);
lean_ctor_set(v_reuseFailAlloc_4134_, 2, v_stop_4055_);
v___x_4077_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
if (lean_obj_tag(v___x_4056_) == 1)
{
lean_object* v_val_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4122_; 
v_val_4078_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4080_ = v___x_4056_;
v_isShared_4081_ = v_isSharedCheck_4122_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_val_4078_);
lean_dec(v___x_4056_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4122_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4082_ = lean_unsigned_to_nat(0u);
v___x_4083_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4084_ = lean_box(0);
v___x_4085_ = lean_array_get(v___x_4084_, v_val_4078_, v___x_4082_);
lean_dec(v_val_4078_);
lean_inc(v_a_4007_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v_a_4007_);
v___x_4087_ = v___x_4080_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4007_);
v___x_4087_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
uint8_t v___x_4088_; 
v___x_4088_ = l_Option_instDecidableEq___redArg(v___x_4083_, v___x_4085_, v___x_4087_);
if (v___x_4088_ == 0)
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
lean_dec_ref(v___x_4077_);
lean_dec_ref(v___x_4060_);
lean_del_object(v___x_4034_);
lean_del_object(v___x_4030_);
lean_dec(v_fst_4028_);
lean_del_object(v___x_4026_);
lean_dec(v_fst_4024_);
v___x_4089_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4090_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4089_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4100_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4093_ = v___x_4090_;
v_isShared_4094_ = v_isSharedCheck_4100_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4090_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4100_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
if (lean_obj_tag(v_a_4091_) == 0)
{
lean_object* v_a_4095_; lean_object* v___x_4097_; 
lean_dec(v_a_4007_);
v_a_4095_ = lean_ctor_get(v_a_4091_, 0);
lean_inc(v_a_4095_);
lean_dec_ref(v_a_4091_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 0, v_a_4095_);
v___x_4097_ = v___x_4093_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4095_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
else
{
lean_object* v_a_4099_; 
lean_del_object(v___x_4093_);
v_a_4099_ = lean_ctor_get(v_a_4091_, 0);
lean_inc(v_a_4099_);
lean_dec_ref(v_a_4091_);
v_a_4015_ = v_a_4099_;
goto v___jp_4014_;
}
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
lean_dec(v_a_4007_);
v_a_4101_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4090_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4090_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4113_; 
lean_inc(v_fst_4028_);
v___x_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_fst_4028_);
v___x_4110_ = lean_array_push(v_fst_4024_, v___x_4109_);
v___x_4111_ = lean_nat_add(v_fst_4028_, v___x_4057_);
lean_dec(v_fst_4028_);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 1, v___x_4060_);
lean_ctor_set(v___x_4034_, 0, v___x_4077_);
v___x_4113_ = v___x_4034_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v___x_4060_);
v___x_4113_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v___x_4115_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v___x_4113_);
lean_ctor_set(v___x_4030_, 0, v___x_4111_);
v___x_4115_ = v___x_4030_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4111_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4117_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4115_);
lean_ctor_set(v___x_4026_, 0, v___x_4110_);
v___x_4117_ = v___x_4026_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4110_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v___x_4115_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
v_a_4015_ = v___x_4117_;
goto v___jp_4014_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4126_; 
lean_dec(v___x_4056_);
v___x_4123_ = lean_box(0);
v___x_4124_ = lean_array_push(v_fst_4024_, v___x_4123_);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 1, v___x_4060_);
lean_ctor_set(v___x_4034_, 0, v___x_4077_);
v___x_4126_ = v___x_4034_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v___x_4060_);
v___x_4126_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
lean_object* v___x_4128_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v___x_4126_);
v___x_4128_ = v___x_4030_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_fst_4028_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v___x_4126_);
v___x_4128_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
lean_object* v___x_4130_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4128_);
lean_ctor_set(v___x_4026_, 0, v___x_4124_);
v___x_4130_ = v___x_4026_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4131_, 1, v___x_4128_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
v_a_4015_ = v___x_4130_;
goto v___jp_4014_;
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
v___jp_4014_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_unsigned_to_nat(1u);
v___x_4017_ = lean_nat_add(v_a_4007_, v___x_4016_);
lean_dec(v_a_4007_);
v_a_4007_ = v___x_4017_;
v_b_4008_ = v_a_4015_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4150_, lean_object* v_a_4151_, lean_object* v_b_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4150_, v_a_4151_, v_b_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v_upperBound_4150_);
return v_res_4158_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4160_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4161_ = lean_unsigned_to_nat(4u);
v___x_4162_ = lean_unsigned_to_nat(275u);
v___x_4163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4164_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4165_ = l_mkPanicMessageWithDecl(v___x_4164_, v___x_4163_, v___x_4162_, v___x_4161_, v___x_4160_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4166_, lean_object* v___x_4167_, lean_object* v___x_4168_, lean_object* v_xs_4169_, lean_object* v_x_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v_graph_4176_; lean_object* v_revDeps_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4230_; 
v_graph_4176_ = lean_ctor_get(v_a_4166_, 0);
v_revDeps_4177_ = lean_ctor_get(v_a_4166_, 1);
v_isSharedCheck_4230_ = !lean_is_exclusive(v_a_4166_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4179_ = v_a_4166_;
v_isShared_4180_ = v_isSharedCheck_4230_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_revDeps_4177_);
lean_inc(v_graph_4176_);
lean_dec(v_a_4166_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4230_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; uint8_t v___x_4184_; 
v___x_4181_ = lean_array_get_borrowed(v___x_4167_, v_graph_4176_, v___x_4168_);
v___x_4182_ = lean_array_get_size(v_xs_4169_);
v___x_4183_ = lean_array_get_size(v___x_4181_);
v___x_4184_ = lean_nat_dec_eq(v___x_4182_, v___x_4183_);
if (v___x_4184_ == 0)
{
lean_object* v___x_4185_; lean_object* v___x_4186_; 
lean_del_object(v___x_4179_);
lean_dec_ref(v_revDeps_4177_);
lean_dec_ref(v_graph_4176_);
lean_dec_ref(v_xs_4169_);
lean_dec(v___x_4168_);
v___x_4185_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4186_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4185_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
return v___x_4186_;
}
else
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4191_; 
v___x_4187_ = lean_mk_empty_array_with_capacity(v___x_4168_);
lean_inc(v___x_4168_);
v___x_4188_ = l_Array_toSubarray___redArg(v_xs_4169_, v___x_4168_, v___x_4182_);
lean_inc(v___x_4168_);
lean_inc(v___x_4181_);
v___x_4189_ = l_Array_toSubarray___redArg(v___x_4181_, v___x_4168_, v___x_4183_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 1, v___x_4189_);
lean_ctor_set(v___x_4179_, 0, v___x_4188_);
v___x_4191_ = v___x_4179_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4229_, 1, v___x_4189_);
v___x_4191_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_inc(v___x_4168_);
v___x_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4168_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4187_);
lean_ctor_set(v___x_4193_, 1, v___x_4192_);
v___x_4194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4182_, v___x_4168_, v___x_4193_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v_snd_4196_; lean_object* v_fst_4197_; lean_object* v_fst_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref(v___x_4194_);
v_snd_4196_ = lean_ctor_get(v_a_4195_, 1);
lean_inc(v_snd_4196_);
v_fst_4197_ = lean_ctor_get(v_a_4195_, 0);
lean_inc(v_fst_4197_);
lean_dec(v_a_4195_);
v_fst_4198_ = lean_ctor_get(v_snd_4196_, 0);
lean_inc(v_fst_4198_);
lean_dec(v_snd_4196_);
v___x_4199_ = lean_unsigned_to_nat(1u);
v___x_4200_ = lean_array_get_size(v_graph_4176_);
v___x_4201_ = lean_mk_empty_array_with_capacity(v___x_4199_);
lean_inc(v_fst_4197_);
v___x_4202_ = lean_array_push(v___x_4201_, v_fst_4197_);
v___x_4203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4200_, v_graph_4176_, v_fst_4197_, v___x_4199_, v___x_4202_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
lean_dec(v_fst_4197_);
lean_dec_ref(v_graph_4176_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4212_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4208_; lean_object* v___x_4210_; 
v___x_4208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4208_, 0, v_fst_4198_);
lean_ctor_set(v___x_4208_, 1, v_a_4204_);
lean_ctor_set(v___x_4208_, 2, v_revDeps_4177_);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v___x_4208_);
v___x_4210_ = v___x_4206_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4208_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec(v_fst_4198_);
lean_dec_ref(v_revDeps_4177_);
v_a_4213_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4203_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4203_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_dec_ref(v_revDeps_4177_);
lean_dec_ref(v_graph_4176_);
v_a_4221_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4194_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4194_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4231_, lean_object* v___x_4232_, lean_object* v___x_4233_, lean_object* v_xs_4234_, lean_object* v_x_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4231_, v___x_4232_, v___x_4233_, v_xs_4234_, v_x_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec_ref(v_x_4235_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_){
_start:
{
lean_object* v___x_4248_; 
lean_inc_ref(v_preDefs_4242_);
v___x_4248_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v_value_4253_; lean_object* v___x_4254_; lean_object* v___f_4255_; uint8_t v___x_4256_; lean_object* v___x_4257_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_a_4249_);
lean_dec_ref(v___x_4248_);
v___x_4250_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4251_ = lean_unsigned_to_nat(0u);
v___x_4252_ = lean_array_get(v___x_4250_, v_preDefs_4242_, v___x_4251_);
lean_dec_ref(v_preDefs_4242_);
v_value_4253_ = lean_ctor_get(v___x_4252_, 7);
lean_inc_ref(v_value_4253_);
lean_dec(v___x_4252_);
v___x_4254_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4255_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4255_, 0, v_a_4249_);
lean_closure_set(v___f_4255_, 1, v___x_4254_);
lean_closure_set(v___f_4255_, 2, v___x_4251_);
v___x_4256_ = 0;
v___x_4257_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4253_, v___f_4255_, v___x_4256_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
return v___x_4257_;
}
else
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
lean_dec_ref(v_preDefs_4242_);
v_a_4258_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4260_ = v___x_4248_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4248_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_);
lean_dec(v_a_4270_);
lean_dec_ref(v_a_4269_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4267_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4273_, lean_object* v___x_4274_, lean_object* v___x_4275_, lean_object* v_inst_4276_, lean_object* v_R_4277_, lean_object* v_a_4278_, lean_object* v_b_4279_, lean_object* v_c_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v___x_4286_; 
v___x_4286_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4273_, v___x_4274_, v___x_4275_, v_a_4278_, v_b_4279_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4287_, lean_object* v___x_4288_, lean_object* v___x_4289_, lean_object* v_inst_4290_, lean_object* v_R_4291_, lean_object* v_a_4292_, lean_object* v_b_4293_, lean_object* v_c_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4287_, v___x_4288_, v___x_4289_, v_inst_4290_, v_R_4291_, v_a_4292_, v_b_4293_, v_c_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec_ref(v___x_4289_);
lean_dec_ref(v___x_4288_);
lean_dec(v_upperBound_4287_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4301_, lean_object* v_inst_4302_, lean_object* v_R_4303_, lean_object* v_a_4304_, lean_object* v_b_4305_, lean_object* v_c_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4301_, v_a_4304_, v_b_4305_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4313_, lean_object* v_inst_4314_, lean_object* v_R_4315_, lean_object* v_a_4316_, lean_object* v_b_4317_, lean_object* v_c_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4313_, v_inst_4314_, v_R_4315_, v_a_4316_, v_b_4317_, v_c_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec(v_upperBound_4313_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4325_, size_t v_i_4326_, size_t v_stop_4327_, lean_object* v_b_4328_){
_start:
{
uint8_t v___x_4329_; 
v___x_4329_ = lean_usize_dec_eq(v_i_4326_, v_stop_4327_);
if (v___x_4329_ == 0)
{
size_t v___x_4330_; size_t v___x_4331_; lean_object* v___x_4332_; 
v___x_4330_ = ((size_t)1ULL);
v___x_4331_ = lean_usize_sub(v_i_4326_, v___x_4330_);
v___x_4332_ = lean_array_uget_borrowed(v_as_4325_, v___x_4331_);
if (lean_obj_tag(v___x_4332_) == 0)
{
v_i_4326_ = v___x_4331_;
goto _start;
}
else
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4334_ = lean_unsigned_to_nat(1u);
v___x_4335_ = lean_nat_add(v_b_4328_, v___x_4334_);
lean_dec(v_b_4328_);
v_i_4326_ = v___x_4331_;
v_b_4328_ = v___x_4335_;
goto _start;
}
}
else
{
return v_b_4328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4337_, lean_object* v_i_4338_, lean_object* v_stop_4339_, lean_object* v_b_4340_){
_start:
{
size_t v_i_boxed_4341_; size_t v_stop_boxed_4342_; lean_object* v_res_4343_; 
v_i_boxed_4341_ = lean_unbox_usize(v_i_4338_);
lean_dec(v_i_4338_);
v_stop_boxed_4342_ = lean_unbox_usize(v_stop_4339_);
lean_dec(v_stop_4339_);
v_res_4343_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4337_, v_i_boxed_4341_, v_stop_boxed_4342_, v_b_4340_);
lean_dec_ref(v_as_4337_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4344_){
_start:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; uint8_t v___x_4347_; 
v___x_4345_ = lean_unsigned_to_nat(0u);
v___x_4346_ = lean_array_get_size(v_perm_4344_);
v___x_4347_ = lean_nat_dec_lt(v___x_4345_, v___x_4346_);
if (v___x_4347_ == 0)
{
return v___x_4345_;
}
else
{
size_t v___x_4348_; size_t v___x_4349_; lean_object* v___x_4350_; 
v___x_4348_ = lean_usize_of_nat(v___x_4346_);
v___x_4349_ = ((size_t)0ULL);
v___x_4350_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4344_, v___x_4348_, v___x_4349_, v___x_4345_);
return v___x_4350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4351_);
lean_dec_ref(v_perm_4351_);
return v_res_4352_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4353_, lean_object* v_i_4354_){
_start:
{
lean_object* v___x_4355_; uint8_t v___x_4356_; 
v___x_4355_ = lean_array_get_size(v_perm_4353_);
v___x_4356_ = lean_nat_dec_lt(v_i_4354_, v___x_4355_);
if (v___x_4356_ == 0)
{
return v___x_4356_;
}
else
{
lean_object* v___x_4357_; 
v___x_4357_ = lean_array_fget_borrowed(v_perm_4353_, v_i_4354_);
if (lean_obj_tag(v___x_4357_) == 0)
{
uint8_t v___x_4358_; 
v___x_4358_ = 0;
return v___x_4358_;
}
else
{
return v___x_4356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4359_, lean_object* v_i_4360_){
_start:
{
uint8_t v_res_4361_; lean_object* v_r_4362_; 
v_res_4361_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4359_, v_i_4360_);
lean_dec(v_i_4360_);
lean_dec_ref(v_perm_4359_);
v_r_4362_ = lean_box(v_res_4361_);
return v_r_4362_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
lean_object* v___f_4369_; lean_object* v___x_1076__overap_4370_; lean_object* v___x_4371_; 
v___f_4369_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_1076__overap_4370_ = lean_panic_fn(v___f_4369_, v_msg_4363_);
lean_inc(v___y_4367_);
lean_inc_ref(v___y_4366_);
lean_inc(v___y_4365_);
lean_inc_ref(v___y_4364_);
v___x_4371_ = lean_apply_5(v___x_1076__overap_4370_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, lean_box(0));
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4379_, lean_object* v_msg_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4387_, lean_object* v_msg_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4387_, v_msg_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4395_, lean_object* v_maxFVars_x3f_4396_, lean_object* v_k_4397_, uint8_t v_cleanupAnnotations_4398_, uint8_t v_whnfType_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v___f_4405_; lean_object* v___x_4406_; 
v___f_4405_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4405_, 0, v_k_4397_);
v___x_4406_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4395_, v_maxFVars_x3f_4396_, v___f_4405_, v_cleanupAnnotations_4398_, v_whnfType_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4406_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4406_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
v_a_4415_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4406_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4406_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4423_, lean_object* v_maxFVars_x3f_4424_, lean_object* v_k_4425_, lean_object* v_cleanupAnnotations_4426_, lean_object* v_whnfType_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4433_; uint8_t v_whnfType_boxed_4434_; lean_object* v_res_4435_; 
v_cleanupAnnotations_boxed_4433_ = lean_unbox(v_cleanupAnnotations_4426_);
v_whnfType_boxed_4434_ = lean_unbox(v_whnfType_4427_);
v_res_4435_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4423_, v_maxFVars_x3f_4424_, v_k_4425_, v_cleanupAnnotations_boxed_4433_, v_whnfType_boxed_4434_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4436_, lean_object* v_type_4437_, lean_object* v_maxFVars_x3f_4438_, lean_object* v_k_4439_, uint8_t v_cleanupAnnotations_4440_, uint8_t v_whnfType_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v___x_4447_; 
v___x_4447_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4437_, v_maxFVars_x3f_4438_, v_k_4439_, v_cleanupAnnotations_4440_, v_whnfType_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4448_, lean_object* v_type_4449_, lean_object* v_maxFVars_x3f_4450_, lean_object* v_k_4451_, lean_object* v_cleanupAnnotations_4452_, lean_object* v_whnfType_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4459_; uint8_t v_whnfType_boxed_4460_; lean_object* v_res_4461_; 
v_cleanupAnnotations_boxed_4459_ = lean_unbox(v_cleanupAnnotations_4452_);
v_whnfType_boxed_4460_ = lean_unbox(v_whnfType_4453_);
v_res_4461_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4448_, v_type_4449_, v_maxFVars_x3f_4450_, v_k_4451_, v_cleanupAnnotations_boxed_4459_, v_whnfType_boxed_4460_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
return v_res_4461_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4464_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4465_ = lean_unsigned_to_nat(6u);
v___x_4466_ = lean_unsigned_to_nat(329u);
v___x_4467_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4468_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4469_ = l_mkPanicMessageWithDecl(v___x_4468_, v___x_4467_, v___x_4466_, v___x_4465_, v___x_4464_);
return v___x_4469_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4473_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4474_ = lean_unsigned_to_nat(8u);
v___x_4475_ = lean_unsigned_to_nat(322u);
v___x_4476_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4477_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4478_ = l_mkPanicMessageWithDecl(v___x_4477_, v___x_4476_, v___x_4475_, v___x_4474_, v___x_4473_);
return v___x_4478_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4480_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4481_ = lean_unsigned_to_nat(8u);
v___x_4482_ = lean_unsigned_to_nat(325u);
v___x_4483_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4484_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4485_ = l_mkPanicMessageWithDecl(v___x_4484_, v___x_4483_, v___x_4482_, v___x_4481_, v___x_4480_);
return v___x_4485_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4487_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4488_ = lean_unsigned_to_nat(8u);
v___x_4489_ = lean_unsigned_to_nat(324u);
v___x_4490_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4491_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4492_ = l_mkPanicMessageWithDecl(v___x_4491_, v___x_4490_, v___x_4489_, v___x_4488_, v___x_4487_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4493_, lean_object* v_xs_4494_, lean_object* v_val_4495_, lean_object* v_i_4496_, lean_object* v_perm_4497_, lean_object* v_k_4498_, lean_object* v_xs_x27_4499_, lean_object* v_type_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v___x_4506_; uint8_t v___x_4507_; 
v___x_4506_ = lean_array_get_size(v_xs_x27_4499_);
v___x_4507_ = lean_nat_dec_eq(v___x_4506_, v___x_4493_);
if (v___x_4507_ == 0)
{
lean_object* v___x_4508_; lean_object* v___x_4509_; 
lean_dec_ref(v_type_4500_);
lean_dec_ref(v_k_4498_);
lean_dec_ref(v_perm_4497_);
lean_dec_ref(v_xs_4494_);
v___x_4508_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4509_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4508_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
return v___x_4509_;
}
else
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v_x_4512_; lean_object* v___x_4513_; 
v___x_4510_ = l_Lean_instInhabitedExpr;
v___x_4511_ = lean_unsigned_to_nat(0u);
v_x_4512_ = lean_array_get_borrowed(v___x_4510_, v_xs_x27_4499_, v___x_4511_);
lean_inc(v___y_4504_);
lean_inc_ref(v___y_4503_);
lean_inc(v___y_4502_);
lean_inc_ref(v___y_4501_);
lean_inc(v_x_4512_);
v___x_4513_ = lean_infer_type(v_x_4512_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; uint8_t v___x_4515_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref(v___x_4513_);
v___x_4515_ = l_Lean_Expr_hasLooseBVars(v_a_4514_);
lean_dec(v_a_4514_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4516_ = lean_array_get_size(v_xs_4494_);
v___x_4517_ = lean_nat_dec_lt(v_val_4495_, v___x_4516_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
lean_dec_ref(v_type_4500_);
lean_dec_ref(v_k_4498_);
lean_dec_ref(v_perm_4497_);
lean_dec_ref(v_xs_4494_);
v___x_4518_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4519_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4518_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
return v___x_4519_;
}
else
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4520_ = lean_nat_add(v_i_4496_, v___x_4493_);
lean_inc(v_x_4512_);
v___x_4521_ = lean_array_set(v_xs_4494_, v_val_4495_, v_x_4512_);
v___x_4522_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4497_, v_k_4498_, v___x_4520_, v_type_4500_, v___x_4521_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
return v___x_4522_;
}
}
else
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
lean_dec_ref(v_type_4500_);
lean_dec_ref(v_k_4498_);
lean_dec_ref(v_perm_4497_);
lean_dec_ref(v_xs_4494_);
v___x_4523_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4524_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4523_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
return v___x_4524_;
}
}
else
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4532_; 
lean_dec_ref(v_type_4500_);
lean_dec_ref(v_k_4498_);
lean_dec_ref(v_perm_4497_);
lean_dec_ref(v_xs_4494_);
v_a_4525_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4527_ = v___x_4513_;
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v___x_4513_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4530_; 
if (v_isShared_4528_ == 0)
{
v___x_4530_ = v___x_4527_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_a_4525_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
return v___x_4530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4533_, lean_object* v_xs_4534_, lean_object* v_val_4535_, lean_object* v_i_4536_, lean_object* v_perm_4537_, lean_object* v_k_4538_, lean_object* v_xs_x27_4539_, lean_object* v_type_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4533_, v_xs_4534_, v_val_4535_, v_i_4536_, v_perm_4537_, v_k_4538_, v_xs_x27_4539_, v_type_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec_ref(v_xs_x27_4539_);
lean_dec(v_i_4536_);
lean_dec(v_val_4535_);
lean_dec(v___x_4533_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4547_, lean_object* v_k_4548_, lean_object* v_i_4549_, lean_object* v_type_4550_, lean_object* v_xs_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_){
_start:
{
lean_object* v___x_4557_; uint8_t v___x_4558_; 
v___x_4557_ = lean_array_get_size(v_perm_4547_);
v___x_4558_ = lean_nat_dec_lt(v_i_4549_, v___x_4557_);
if (v___x_4558_ == 0)
{
lean_object* v___x_4559_; 
lean_dec_ref(v_type_4550_);
lean_dec(v_i_4549_);
lean_dec_ref(v_perm_4547_);
lean_inc(v_a_4555_);
lean_inc_ref(v_a_4554_);
lean_inc(v_a_4553_);
lean_inc_ref(v_a_4552_);
v___x_4559_ = lean_apply_6(v_k_4548_, v_xs_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, lean_box(0));
return v___x_4559_;
}
else
{
lean_object* v___x_4560_; 
v___x_4560_ = lean_array_fget_borrowed(v_perm_4547_, v_i_4549_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v___x_4561_; 
lean_inc(v_a_4555_);
lean_inc_ref(v_a_4554_);
lean_inc(v_a_4553_);
lean_inc_ref(v_a_4552_);
v___x_4561_ = lean_whnf(v_type_4550_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v_a_4562_; uint8_t v___x_4563_; 
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_a_4562_);
lean_dec_ref(v___x_4561_);
v___x_4563_ = l_Lean_Expr_isForall(v_a_4562_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
lean_dec(v_a_4562_);
lean_dec_ref(v_xs_4551_);
lean_dec(v_i_4549_);
lean_dec_ref(v_k_4548_);
lean_dec_ref(v_perm_4547_);
v___x_4564_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4565_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4564_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_);
return v___x_4565_;
}
else
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4566_ = lean_unsigned_to_nat(1u);
v___x_4567_ = lean_nat_add(v_i_4549_, v___x_4566_);
lean_dec(v_i_4549_);
v___x_4568_ = l_Lean_Expr_bindingBody_x21(v_a_4562_);
lean_dec(v_a_4562_);
v_i_4549_ = v___x_4567_;
v_type_4550_ = v___x_4568_;
goto _start;
}
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
lean_dec_ref(v_xs_4551_);
lean_dec(v_i_4549_);
lean_dec_ref(v_k_4548_);
lean_dec_ref(v_perm_4547_);
v_a_4570_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4561_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4561_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
else
{
lean_object* v_val_4578_; lean_object* v___x_4579_; lean_object* v___f_4580_; lean_object* v___x_4581_; uint8_t v___x_4582_; lean_object* v___x_4583_; 
v_val_4578_ = lean_ctor_get(v___x_4560_, 0);
lean_inc(v_val_4578_);
v___x_4579_ = lean_unsigned_to_nat(1u);
v___f_4580_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4580_, 0, v___x_4579_);
lean_closure_set(v___f_4580_, 1, v_xs_4551_);
lean_closure_set(v___f_4580_, 2, v_val_4578_);
lean_closure_set(v___f_4580_, 3, v_i_4549_);
lean_closure_set(v___f_4580_, 4, v_perm_4547_);
lean_closure_set(v___f_4580_, 5, v_k_4548_);
v___x_4581_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4582_ = 0;
v___x_4583_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4550_, v___x_4581_, v___f_4580_, v___x_4558_, v___x_4582_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_);
return v___x_4583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4584_, lean_object* v_k_4585_, lean_object* v_i_4586_, lean_object* v_type_4587_, lean_object* v_xs_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4584_, v_k_4585_, v_i_4586_, v_type_4587_, v_xs_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4595_, lean_object* v_perm_4596_, lean_object* v_k_4597_, lean_object* v_i_4598_, lean_object* v_type_4599_, lean_object* v_xs_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v___x_4606_; 
v___x_4606_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4596_, v_k_4597_, v_i_4598_, v_type_4599_, v_xs_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_);
return v___x_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4607_, lean_object* v_perm_4608_, lean_object* v_k_4609_, lean_object* v_i_4610_, lean_object* v_type_4611_, lean_object* v_xs_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4607_, v_perm_4608_, v_k_4609_, v_i_4610_, v_type_4611_, v_xs_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec(v_a_4614_);
lean_dec_ref(v_a_4613_);
return v_res_4618_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4619_ = lean_unsigned_to_nat(0u);
v___x_4620_ = l_Lean_Level_ofNat(v___x_4619_);
return v___x_4620_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4621_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4622_ = l_Lean_mkSort(v___x_4621_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4623_, lean_object* v_type_4624_, lean_object* v_k_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_){
_start:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4631_ = lean_unsigned_to_nat(0u);
v___x_4632_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4623_);
v___x_4633_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4634_ = lean_mk_array(v___x_4632_, v___x_4633_);
v___x_4635_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4623_, v_k_4625_, v___x_4631_, v_type_4624_, v___x_4634_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4636_, lean_object* v_type_4637_, lean_object* v_k_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4636_, v_type_4637_, v_k_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_);
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
lean_dec(v_a_4640_);
lean_dec_ref(v_a_4639_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4645_, lean_object* v_perm_4646_, lean_object* v_type_4647_, lean_object* v_k_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
lean_object* v___x_4654_; 
v___x_4654_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4646_, v_type_4647_, v_k_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4655_, lean_object* v_perm_4656_, lean_object* v_type_4657_, lean_object* v_k_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4655_, v_perm_4656_, v_type_4657_, v_k_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4665_, lean_object* v_runInBase_4666_, lean_object* v_b_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4673_ = lean_apply_1(v_k_4665_, v_b_4667_);
lean_inc(v___y_4671_);
lean_inc_ref(v___y_4670_);
lean_inc(v___y_4669_);
lean_inc_ref(v___y_4668_);
v___x_4674_ = lean_apply_7(v_runInBase_4666_, lean_box(0), v___x_4673_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, lean_box(0));
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4675_, lean_object* v_runInBase_4676_, lean_object* v_b_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4675_, v_runInBase_4676_, v_b_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4684_, lean_object* v_perm_4685_, lean_object* v_type_4686_, lean_object* v_runInBase_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
lean_object* v___f_4693_; lean_object* v___x_4694_; 
v___f_4693_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4693_, 0, v_k_4684_);
lean_closure_set(v___f_4693_, 1, v_runInBase_4687_);
v___x_4694_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4685_, v_type_4686_, v___f_4693_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
return v___x_4694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4695_, lean_object* v_perm_4696_, lean_object* v_type_4697_, lean_object* v_runInBase_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4695_, v_perm_4696_, v_type_4697_, v_runInBase_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
lean_dec(v___y_4700_);
lean_dec_ref(v___y_4699_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4705_, lean_object* v_inst_4706_, lean_object* v_perm_4707_, lean_object* v_type_4708_, lean_object* v_k_4709_){
_start:
{
lean_object* v_toBind_4710_; lean_object* v_liftWith_4711_; lean_object* v_restoreM_4712_; lean_object* v___f_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v_toBind_4710_ = lean_ctor_get(v_inst_4706_, 1);
lean_inc(v_toBind_4710_);
lean_dec_ref(v_inst_4706_);
v_liftWith_4711_ = lean_ctor_get(v_inst_4705_, 0);
lean_inc(v_liftWith_4711_);
v_restoreM_4712_ = lean_ctor_get(v_inst_4705_, 1);
lean_inc(v_restoreM_4712_);
lean_dec_ref(v_inst_4705_);
v___f_4713_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4713_, 0, v_k_4709_);
lean_closure_set(v___f_4713_, 1, v_perm_4707_);
lean_closure_set(v___f_4713_, 2, v_type_4708_);
v___x_4714_ = lean_apply_2(v_liftWith_4711_, lean_box(0), v___f_4713_);
v___x_4715_ = lean_apply_1(v_restoreM_4712_, lean_box(0));
v___x_4716_ = lean_apply_4(v_toBind_4710_, lean_box(0), lean_box(0), v___x_4714_, v___x_4715_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4717_, lean_object* v_00_u03b1_4718_, lean_object* v_inst_4719_, lean_object* v_inst_4720_, lean_object* v_perm_4721_, lean_object* v_type_4722_, lean_object* v_k_4723_){
_start:
{
lean_object* v___x_4724_; 
v___x_4724_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4719_, v_inst_4720_, v_perm_4721_, v_type_4722_, v_k_4723_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
lean_object* v___f_4731_; lean_object* v___x_603__overap_4732_; lean_object* v___x_4733_; 
v___f_4731_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_603__overap_4732_ = lean_panic_fn(v___f_4731_, v_msg_4725_);
lean_inc(v___y_4729_);
lean_inc_ref(v___y_4728_);
lean_inc(v___y_4727_);
lean_inc_ref(v___y_4726_);
v___x_4733_ = lean_apply_5(v___x_603__overap_4732_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, lean_box(0));
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v_res_4740_; 
v_res_4740_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
return v_res_4740_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4743_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4744_ = lean_unsigned_to_nat(10u);
v___x_4745_ = lean_unsigned_to_nat(353u);
v___x_4746_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4747_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4748_ = l_mkPanicMessageWithDecl(v___x_4747_, v___x_4746_, v___x_4745_, v___x_4744_, v___x_4743_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4749_, lean_object* v_xs_4750_, lean_object* v_tail_4751_, lean_object* v_ys_4752_, lean_object* v_type_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_){
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4749_, v_xs_4750_, v_tail_4751_, v_ys_4752_, v_type_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
lean_dec(v___y_4757_);
lean_dec_ref(v___y_4756_);
lean_dec(v___y_4755_);
lean_dec_ref(v___y_4754_);
lean_dec_ref(v_ys_4752_);
lean_dec(v___x_4749_);
return v_res_4759_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4760_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4761_ = lean_unsigned_to_nat(8u);
v___x_4762_ = lean_unsigned_to_nat(349u);
v___x_4763_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4764_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4765_ = l_mkPanicMessageWithDecl(v___x_4764_, v___x_4763_, v___x_4762_, v___x_4761_, v___x_4760_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4766_, lean_object* v_x_4767_, lean_object* v_x_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_){
_start:
{
if (lean_obj_tag(v_x_4767_) == 0)
{
lean_object* v___x_4774_; 
lean_dec_ref(v_xs_4766_);
v___x_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4774_, 0, v_x_4768_);
return v___x_4774_;
}
else
{
lean_object* v_head_4775_; 
v_head_4775_ = lean_ctor_get(v_x_4767_, 0);
if (lean_obj_tag(v_head_4775_) == 0)
{
lean_object* v_tail_4776_; lean_object* v___x_4777_; lean_object* v___f_4778_; lean_object* v___x_4779_; uint8_t v___x_4780_; lean_object* v___x_4781_; 
v_tail_4776_ = lean_ctor_get(v_x_4767_, 1);
lean_inc(v_tail_4776_);
lean_dec_ref(v_x_4767_);
v___x_4777_ = lean_unsigned_to_nat(1u);
v___f_4778_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4778_, 0, v___x_4777_);
lean_closure_set(v___f_4778_, 1, v_xs_4766_);
lean_closure_set(v___f_4778_, 2, v_tail_4776_);
v___x_4779_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4780_ = 0;
v___x_4781_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4768_, v___x_4779_, v___f_4778_, v___x_4780_, v___x_4780_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
return v___x_4781_;
}
else
{
lean_object* v_tail_4782_; lean_object* v_val_4783_; lean_object* v___x_4784_; uint8_t v___x_4785_; 
lean_inc_ref(v_head_4775_);
v_tail_4782_ = lean_ctor_get(v_x_4767_, 1);
lean_inc(v_tail_4782_);
lean_dec_ref(v_x_4767_);
v_val_4783_ = lean_ctor_get(v_head_4775_, 0);
lean_inc(v_val_4783_);
lean_dec_ref(v_head_4775_);
v___x_4784_ = lean_array_get_size(v_xs_4766_);
v___x_4785_ = lean_nat_dec_lt(v_val_4783_, v___x_4784_);
if (v___x_4785_ == 0)
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
lean_dec(v_val_4783_);
lean_dec(v_tail_4782_);
lean_dec_ref(v_x_4768_);
lean_dec_ref(v_xs_4766_);
v___x_4786_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4787_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4786_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
return v___x_4787_;
}
else
{
lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4788_ = l_Lean_instInhabitedExpr;
v___x_4789_ = lean_array_get_borrowed(v___x_4788_, v_xs_4766_, v_val_4783_);
lean_dec(v_val_4783_);
v___x_4790_ = lean_unsigned_to_nat(1u);
v___x_4791_ = lean_mk_empty_array_with_capacity(v___x_4790_);
lean_inc(v___x_4789_);
v___x_4792_ = lean_array_push(v___x_4791_, v___x_4789_);
v___x_4793_ = l_Lean_Meta_instantiateForall(v_x_4768_, v___x_4792_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
lean_dec_ref(v___x_4792_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; 
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
lean_inc(v_a_4794_);
lean_dec_ref(v___x_4793_);
v_x_4767_ = v_tail_4782_;
v_x_4768_ = v_a_4794_;
goto _start;
}
else
{
lean_dec(v_tail_4782_);
lean_dec_ref(v_xs_4766_);
return v___x_4793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4796_, lean_object* v_xs_4797_, lean_object* v_tail_4798_, lean_object* v_ys_4799_, lean_object* v_type_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v___x_4806_; uint8_t v___x_4807_; 
v___x_4806_ = lean_array_get_size(v_ys_4799_);
v___x_4807_ = lean_nat_dec_eq(v___x_4806_, v___x_4796_);
if (v___x_4807_ == 0)
{
lean_object* v___x_4808_; lean_object* v___x_4809_; 
lean_dec_ref(v_type_4800_);
lean_dec(v_tail_4798_);
lean_dec_ref(v_xs_4797_);
v___x_4808_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4809_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4808_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
return v___x_4809_;
}
else
{
lean_object* v___x_4810_; 
v___x_4810_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4797_, v_tail_4798_, v_type_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; uint8_t v___x_4812_; uint8_t v___x_4813_; lean_object* v___x_4814_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
lean_inc(v_a_4811_);
lean_dec_ref(v___x_4810_);
v___x_4812_ = 0;
v___x_4813_ = 1;
v___x_4814_ = l_Lean_Meta_mkForallFVars(v_ys_4799_, v_a_4811_, v___x_4812_, v___x_4807_, v___x_4807_, v___x_4813_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
return v___x_4814_;
}
else
{
return v___x_4810_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4815_, lean_object* v_x_4816_, lean_object* v_x_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_){
_start:
{
lean_object* v_res_4823_; 
v_res_4823_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4815_, v_x_4816_, v_x_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_);
lean_dec(v_a_4821_);
lean_dec_ref(v_a_4820_);
lean_dec(v_a_4819_);
lean_dec_ref(v_a_4818_);
return v_res_4823_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4826_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4827_ = lean_unsigned_to_nat(2u);
v___x_4828_ = lean_unsigned_to_nat(343u);
v___x_4829_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4830_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4831_ = l_mkPanicMessageWithDecl(v___x_4830_, v___x_4829_, v___x_4828_, v___x_4827_, v___x_4826_);
return v___x_4831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4832_, lean_object* v_type_u2080_4833_, lean_object* v_xs_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_){
_start:
{
lean_object* v___x_4840_; lean_object* v___x_4841_; uint8_t v___x_4842_; 
v___x_4840_ = lean_array_get_size(v_xs_4834_);
v___x_4841_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4832_);
v___x_4842_ = lean_nat_dec_eq(v___x_4840_, v___x_4841_);
lean_dec(v___x_4841_);
if (v___x_4842_ == 0)
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
lean_dec_ref(v_xs_4834_);
lean_dec_ref(v_type_u2080_4833_);
lean_dec_ref(v_perm_4832_);
v___x_4843_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4844_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4843_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
return v___x_4844_;
}
else
{
lean_object* v_mask_4845_; lean_object* v___x_4846_; 
v_mask_4845_ = lean_array_to_list(v_perm_4832_);
v___x_4846_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4834_, v_mask_4845_, v_type_u2080_4833_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
return v___x_4846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4847_, lean_object* v_type_u2080_4848_, lean_object* v_xs_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4847_, v_type_u2080_4848_, v_xs_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(lean_object* v_e_4856_, lean_object* v_maxFVars_4857_, lean_object* v_k_4858_, uint8_t v_cleanupAnnotations_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v___f_4865_; uint8_t v___x_4866_; uint8_t v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___f_4865_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4865_, 0, v_k_4858_);
v___x_4866_ = 1;
v___x_4867_ = 0;
v___x_4868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4868_, 0, v_maxFVars_4857_);
v___x_4869_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4856_, v___x_4866_, v___x_4867_, v___x_4866_, v___x_4867_, v___x_4868_, v___f_4865_, v_cleanupAnnotations_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
lean_dec_ref(v___x_4868_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4877_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4877_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4877_ == 0)
{
v___x_4872_ = v___x_4869_;
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_a_4870_);
lean_dec(v___x_4869_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4875_; 
if (v_isShared_4873_ == 0)
{
v___x_4875_ = v___x_4872_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v_a_4870_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
}
else
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4885_; 
v_a_4878_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4880_ = v___x_4869_;
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4869_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4883_; 
if (v_isShared_4881_ == 0)
{
v___x_4883_ = v___x_4880_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_a_4878_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg___boxed(lean_object* v_e_4886_, lean_object* v_maxFVars_4887_, lean_object* v_k_4888_, lean_object* v_cleanupAnnotations_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4895_; lean_object* v_res_4896_; 
v_cleanupAnnotations_boxed_4895_ = lean_unbox(v_cleanupAnnotations_4889_);
v_res_4896_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(v_e_4886_, v_maxFVars_4887_, v_k_4888_, v_cleanupAnnotations_boxed_4895_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
lean_dec(v___y_4891_);
lean_dec_ref(v___y_4890_);
return v_res_4896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_00_u03b1_4897_, lean_object* v_e_4898_, lean_object* v_maxFVars_4899_, lean_object* v_k_4900_, uint8_t v_cleanupAnnotations_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
lean_object* v___x_4907_; 
v___x_4907_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(v_e_4898_, v_maxFVars_4899_, v_k_4900_, v_cleanupAnnotations_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_00_u03b1_4908_, lean_object* v_e_4909_, lean_object* v_maxFVars_4910_, lean_object* v_k_4911_, lean_object* v_cleanupAnnotations_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4918_; lean_object* v_res_4919_; 
v_cleanupAnnotations_boxed_4918_ = lean_unbox(v_cleanupAnnotations_4912_);
v_res_4919_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_00_u03b1_4908_, v_e_4909_, v_maxFVars_4910_, v_k_4911_, v_cleanupAnnotations_boxed_4918_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
lean_dec(v___y_4916_);
lean_dec_ref(v___y_4915_);
lean_dec(v___y_4914_);
lean_dec_ref(v___y_4913_);
return v_res_4919_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___y_4920_){
_start:
{
if (lean_obj_tag(v___y_4920_) == 0)
{
uint8_t v___x_4921_; 
v___x_4921_ = 1;
return v___x_4921_;
}
else
{
uint8_t v___x_4922_; 
v___x_4922_ = 0;
return v___x_4922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___y_4923_){
_start:
{
uint8_t v_res_4924_; lean_object* v_r_4925_; 
v_res_4924_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___y_4923_);
lean_dec(v___y_4923_);
v_r_4925_ = lean_box(v_res_4924_);
return v_r_4925_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2(void){
_start:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4928_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__1));
v___x_4929_ = lean_unsigned_to_nat(12u);
v___x_4930_ = lean_unsigned_to_nat(376u);
v___x_4931_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__0));
v___x_4932_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4933_ = l_mkPanicMessageWithDecl(v___x_4932_, v___x_4931_, v___x_4930_, v___x_4929_, v___x_4928_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___boxed(lean_object* v___x_4935_, lean_object* v_xs_4936_, lean_object* v_tail_4937_, lean_object* v___x_4938_, lean_object* v___x_4939_, lean_object* v_ys_4940_, lean_object* v_value_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_){
_start:
{
uint8_t v___x_1280__boxed_4947_; uint8_t v___x_1281__boxed_4948_; lean_object* v_res_4949_; 
v___x_1280__boxed_4947_ = lean_unbox(v___x_4938_);
v___x_1281__boxed_4948_ = lean_unbox(v___x_4939_);
v_res_4949_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1(v___x_4935_, v_xs_4936_, v_tail_4937_, v___x_1280__boxed_4947_, v___x_1281__boxed_4948_, v_ys_4940_, v_value_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_);
lean_dec(v___y_4945_);
lean_dec_ref(v___y_4944_);
lean_dec(v___y_4943_);
lean_dec_ref(v___y_4942_);
lean_dec_ref(v_ys_4940_);
lean_dec(v___x_4935_);
return v_res_4949_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1(void){
_start:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4950_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4951_ = lean_unsigned_to_nat(8u);
v___x_4952_ = lean_unsigned_to_nat(368u);
v___x_4953_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__0));
v___x_4954_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4955_ = l_mkPanicMessageWithDecl(v___x_4954_, v___x_4953_, v___x_4952_, v___x_4951_, v___x_4950_);
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4956_, lean_object* v_x_4957_, lean_object* v_x_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_){
_start:
{
if (lean_obj_tag(v_x_4957_) == 0)
{
lean_object* v___x_4964_; 
lean_dec_ref(v_xs_4956_);
v___x_4964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4964_, 0, v_x_4958_);
return v___x_4964_;
}
else
{
lean_object* v_head_4965_; 
v_head_4965_ = lean_ctor_get(v_x_4957_, 0);
if (lean_obj_tag(v_head_4965_) == 0)
{
lean_object* v_tail_4966_; lean_object* v___f_4967_; uint8_t v___x_4968_; 
v_tail_4966_ = lean_ctor_get(v_x_4957_, 1);
lean_inc(v_tail_4966_);
lean_dec_ref(v_x_4957_);
v___f_4967_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0));
lean_inc(v_tail_4966_);
v___x_4968_ = l_List_all___redArg(v_tail_4966_, v___f_4967_);
if (v___x_4968_ == 0)
{
uint8_t v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___f_4973_; lean_object* v___x_4974_; 
v___x_4969_ = 1;
v___x_4970_ = lean_unsigned_to_nat(1u);
v___x_4971_ = lean_box(v___x_4968_);
v___x_4972_ = lean_box(v___x_4969_);
v___f_4973_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4973_, 0, v___x_4970_);
lean_closure_set(v___f_4973_, 1, v_xs_4956_);
lean_closure_set(v___f_4973_, 2, v_tail_4966_);
lean_closure_set(v___f_4973_, 3, v___x_4971_);
lean_closure_set(v___f_4973_, 4, v___x_4972_);
v___x_4974_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___redArg(v_x_4958_, v___x_4970_, v___f_4973_, v___x_4968_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
return v___x_4974_;
}
else
{
lean_object* v___x_4975_; 
lean_dec(v_tail_4966_);
lean_dec_ref(v_xs_4956_);
v___x_4975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4975_, 0, v_x_4958_);
return v___x_4975_;
}
}
else
{
lean_object* v_tail_4976_; lean_object* v_val_4977_; lean_object* v___x_4978_; uint8_t v___x_4979_; 
lean_inc_ref(v_head_4965_);
v_tail_4976_ = lean_ctor_get(v_x_4957_, 1);
lean_inc(v_tail_4976_);
lean_dec_ref(v_x_4957_);
v_val_4977_ = lean_ctor_get(v_head_4965_, 0);
lean_inc(v_val_4977_);
lean_dec_ref(v_head_4965_);
v___x_4978_ = lean_array_get_size(v_xs_4956_);
v___x_4979_ = lean_nat_dec_lt(v_val_4977_, v___x_4978_);
if (v___x_4979_ == 0)
{
lean_object* v___x_4980_; lean_object* v___x_4981_; 
lean_dec(v_val_4977_);
lean_dec(v_tail_4976_);
lean_dec_ref(v_x_4958_);
lean_dec_ref(v_xs_4956_);
v___x_4980_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__1);
v___x_4981_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4980_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
return v___x_4981_;
}
else
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; 
v___x_4982_ = l_Lean_instInhabitedExpr;
v___x_4983_ = lean_array_get_borrowed(v___x_4982_, v_xs_4956_, v_val_4977_);
lean_dec(v_val_4977_);
v___x_4984_ = lean_unsigned_to_nat(1u);
v___x_4985_ = lean_mk_empty_array_with_capacity(v___x_4984_);
lean_inc(v___x_4983_);
v___x_4986_ = lean_array_push(v___x_4985_, v___x_4983_);
v___x_4987_ = l_Lean_Meta_instantiateLambda(v_x_4958_, v___x_4986_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
lean_dec_ref(v___x_4986_);
if (lean_obj_tag(v___x_4987_) == 0)
{
lean_object* v_a_4988_; 
v_a_4988_ = lean_ctor_get(v___x_4987_, 0);
lean_inc(v_a_4988_);
lean_dec_ref(v___x_4987_);
v_x_4957_ = v_tail_4976_;
v_x_4958_ = v_a_4988_;
goto _start;
}
else
{
lean_dec(v_tail_4976_);
lean_dec_ref(v_xs_4956_);
return v___x_4987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1(lean_object* v___x_4990_, lean_object* v_xs_4991_, lean_object* v_tail_4992_, uint8_t v___x_4993_, uint8_t v___x_4994_, lean_object* v_ys_4995_, lean_object* v_value_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_){
_start:
{
lean_object* v___x_5002_; uint8_t v___x_5003_; 
v___x_5002_ = lean_array_get_size(v_ys_4995_);
v___x_5003_ = lean_nat_dec_eq(v___x_5002_, v___x_4990_);
if (v___x_5003_ == 0)
{
lean_object* v___x_5004_; lean_object* v___x_5005_; 
lean_dec_ref(v_value_4996_);
lean_dec(v_tail_4992_);
lean_dec_ref(v_xs_4991_);
v___x_5004_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__1___closed__2);
v___x_5005_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5004_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
return v___x_5005_;
}
else
{
lean_object* v___x_5006_; 
v___x_5006_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4991_, v_tail_4992_, v_value_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
if (lean_obj_tag(v___x_5006_) == 0)
{
lean_object* v_a_5007_; uint8_t v___x_5008_; lean_object* v___x_5009_; 
v_a_5007_ = lean_ctor_get(v___x_5006_, 0);
lean_inc(v_a_5007_);
lean_dec_ref(v___x_5006_);
v___x_5008_ = 1;
v___x_5009_ = l_Lean_Meta_mkLambdaFVars(v_ys_4995_, v_a_5007_, v___x_4993_, v___x_4994_, v___x_4993_, v___x_4994_, v___x_5008_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
return v___x_5009_;
}
else
{
return v___x_5006_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_5010_, lean_object* v_x_5011_, lean_object* v_x_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_){
_start:
{
lean_object* v_res_5018_; 
v_res_5018_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5010_, v_x_5011_, v_x_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_);
lean_dec(v_a_5016_);
lean_dec_ref(v_a_5015_);
lean_dec(v_a_5014_);
lean_dec_ref(v_a_5013_);
return v_res_5018_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5020_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_5021_ = lean_unsigned_to_nat(2u);
v___x_5022_ = lean_unsigned_to_nat(362u);
v___x_5023_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_5024_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5025_ = l_mkPanicMessageWithDecl(v___x_5024_, v___x_5023_, v___x_5022_, v___x_5021_, v___x_5020_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_5026_, lean_object* v_value_u2080_5027_, lean_object* v_xs_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_){
_start:
{
lean_object* v___x_5034_; lean_object* v___x_5035_; uint8_t v___x_5036_; 
v___x_5034_ = lean_array_get_size(v_xs_5028_);
v___x_5035_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5026_);
v___x_5036_ = lean_nat_dec_eq(v___x_5034_, v___x_5035_);
lean_dec(v___x_5035_);
if (v___x_5036_ == 0)
{
lean_object* v___x_5037_; lean_object* v___x_5038_; 
lean_dec_ref(v_xs_5028_);
lean_dec_ref(v_value_u2080_5027_);
lean_dec_ref(v_perm_5026_);
v___x_5037_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_5038_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5037_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
return v___x_5038_;
}
else
{
lean_object* v_mask_5039_; lean_object* v___x_5040_; 
v_mask_5039_ = lean_array_to_list(v_perm_5026_);
v___x_5040_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5028_, v_mask_5039_, v_value_u2080_5027_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
return v___x_5040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_5041_, lean_object* v_value_u2080_5042_, lean_object* v_xs_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_){
_start:
{
lean_object* v_res_5049_; 
v_res_5049_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_5041_, v_value_u2080_5042_, v_xs_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_);
lean_dec(v_a_5047_);
lean_dec_ref(v_a_5046_);
lean_dec(v_a_5045_);
lean_dec_ref(v_a_5044_);
return v_res_5049_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_5057_; 
v___x_5057_ = l_Array_instInhabited(lean_box(0));
return v___x_5057_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5058_){
_start:
{
lean_object* v___f_5059_; lean_object* v___f_5060_; lean_object* v___f_5061_; lean_object* v___f_5062_; lean_object* v___f_5063_; lean_object* v___f_5064_; lean_object* v___f_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___f_5059_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5060_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5061_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5062_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5063_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5064_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5065_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5066_, 0, v___f_5059_);
lean_ctor_set(v___x_5066_, 1, v___f_5060_);
v___x_5067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5066_);
lean_ctor_set(v___x_5067_, 1, v___f_5061_);
lean_ctor_set(v___x_5067_, 2, v___f_5062_);
lean_ctor_set(v___x_5067_, 3, v___f_5063_);
lean_ctor_set(v___x_5067_, 4, v___f_5064_);
v___x_5068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5067_);
lean_ctor_set(v___x_5068_, 1, v___f_5065_);
v___x_5069_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5070_ = l_instInhabitedOfMonad___redArg(v___x_5068_, v___x_5069_);
v___x_5071_ = lean_panic_fn(v___x_5070_, v_msg_5058_);
return v___x_5071_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5072_, lean_object* v_msg_5073_){
_start:
{
lean_object* v___x_5074_; 
v___x_5074_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5073_);
return v___x_5074_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5077_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5078_ = lean_unsigned_to_nat(8u);
v___x_5079_ = lean_unsigned_to_nat(394u);
v___x_5080_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5081_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5082_ = l_mkPanicMessageWithDecl(v___x_5081_, v___x_5080_, v___x_5079_, v___x_5078_, v___x_5077_);
return v___x_5082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5083_, lean_object* v_x_5084_){
_start:
{
if (lean_obj_tag(v_x_5083_) == 0)
{
return v_x_5084_;
}
else
{
lean_object* v_head_5085_; lean_object* v_fst_5086_; 
v_head_5085_ = lean_ctor_get(v_x_5083_, 0);
v_fst_5086_ = lean_ctor_get(v_head_5085_, 0);
if (lean_obj_tag(v_fst_5086_) == 0)
{
lean_object* v_tail_5087_; 
v_tail_5087_ = lean_ctor_get(v_x_5083_, 1);
lean_inc(v_tail_5087_);
lean_dec_ref(v_x_5083_);
v_x_5083_ = v_tail_5087_;
goto _start;
}
else
{
lean_object* v_tail_5089_; lean_object* v_snd_5090_; lean_object* v_val_5091_; lean_object* v___x_5092_; uint8_t v___x_5093_; 
lean_inc_ref(v_fst_5086_);
lean_inc(v_head_5085_);
v_tail_5089_ = lean_ctor_get(v_x_5083_, 1);
lean_inc(v_tail_5089_);
lean_dec_ref(v_x_5083_);
v_snd_5090_ = lean_ctor_get(v_head_5085_, 1);
lean_inc(v_snd_5090_);
lean_dec(v_head_5085_);
v_val_5091_ = lean_ctor_get(v_fst_5086_, 0);
lean_inc(v_val_5091_);
lean_dec_ref(v_fst_5086_);
v___x_5092_ = lean_array_get_size(v_x_5084_);
v___x_5093_ = lean_nat_dec_lt(v_val_5091_, v___x_5092_);
if (v___x_5093_ == 0)
{
lean_object* v___x_5094_; lean_object* v___x_5095_; 
lean_dec(v_val_5091_);
lean_dec(v_snd_5090_);
lean_dec(v_tail_5089_);
lean_dec_ref(v_x_5084_);
v___x_5094_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5095_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5094_);
return v___x_5095_;
}
else
{
lean_object* v___x_5096_; 
v___x_5096_ = lean_array_set(v_x_5084_, v_val_5091_, v_snd_5090_);
lean_dec(v_val_5091_);
v_x_5083_ = v_tail_5089_;
v_x_5084_ = v___x_5096_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5098_, lean_object* v_x_5099_, lean_object* v_x_5100_){
_start:
{
lean_object* v___x_5101_; 
v___x_5101_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5099_, v_x_5100_);
return v___x_5101_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
v___x_5104_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5105_ = lean_unsigned_to_nat(2u);
v___x_5106_ = lean_unsigned_to_nat(384u);
v___x_5107_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5108_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5109_ = l_mkPanicMessageWithDecl(v___x_5108_, v___x_5107_, v___x_5106_, v___x_5105_, v___x_5104_);
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5112_, lean_object* v_xs_5113_){
_start:
{
lean_object* v___x_5114_; lean_object* v___x_5115_; uint8_t v___x_5116_; 
v___x_5114_ = lean_array_get_size(v_xs_5113_);
v___x_5115_ = lean_array_get_size(v_perm_5112_);
v___x_5116_ = lean_nat_dec_eq(v___x_5114_, v___x_5115_);
if (v___x_5116_ == 0)
{
lean_object* v___x_5117_; lean_object* v___x_5118_; 
v___x_5117_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5118_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5117_);
return v___x_5118_;
}
else
{
lean_object* v___x_5119_; uint8_t v___x_5120_; 
v___x_5119_ = lean_unsigned_to_nat(0u);
v___x_5120_ = lean_nat_dec_eq(v___x_5114_, v___x_5119_);
if (v___x_5120_ == 0)
{
lean_object* v_dummy_5121_; lean_object* v___x_5122_; lean_object* v_ys_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; 
v_dummy_5121_ = lean_array_fget_borrowed(v_xs_5113_, v___x_5119_);
v___x_5122_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5112_);
lean_inc(v_dummy_5121_);
v_ys_5123_ = lean_mk_array(v___x_5122_, v_dummy_5121_);
v___x_5124_ = l_Array_zip___redArg(v_perm_5112_, v_xs_5113_);
v___x_5125_ = lean_array_to_list(v___x_5124_);
v___x_5126_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5125_, v_ys_5123_);
return v___x_5126_;
}
else
{
lean_object* v___x_5127_; 
v___x_5127_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5128_, lean_object* v_xs_5129_){
_start:
{
lean_object* v_res_5130_; 
v_res_5130_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5128_, v_xs_5129_);
lean_dec_ref(v_xs_5129_);
lean_dec_ref(v_perm_5128_);
return v_res_5130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5131_, lean_object* v_perm_5132_, lean_object* v_xs_5133_){
_start:
{
lean_object* v___x_5134_; 
v___x_5134_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5132_, v_xs_5133_);
return v___x_5134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5135_, lean_object* v_perm_5136_, lean_object* v_xs_5137_){
_start:
{
lean_object* v_res_5138_; 
v_res_5138_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5135_, v_perm_5136_, v_xs_5137_);
lean_dec_ref(v_xs_5137_);
lean_dec_ref(v_perm_5136_);
return v_res_5138_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5139_, lean_object* v_upperBound_5140_, lean_object* v_perm_5141_, lean_object* v_a_5142_, lean_object* v_b_5143_){
_start:
{
lean_object* v_a_5145_; uint8_t v___x_5152_; 
v___x_5152_ = lean_nat_dec_lt(v_a_5142_, v_upperBound_5140_);
if (v___x_5152_ == 0)
{
lean_dec(v_a_5142_);
return v_b_5143_;
}
else
{
lean_object* v___x_5153_; uint8_t v___x_5154_; 
v___x_5153_ = lean_array_get_size(v_perm_5141_);
v___x_5154_ = lean_nat_dec_lt(v_a_5142_, v___x_5153_);
if (v___x_5154_ == 0)
{
goto v___jp_5149_;
}
else
{
lean_object* v___x_5155_; 
v___x_5155_ = lean_array_fget_borrowed(v_perm_5141_, v_a_5142_);
if (lean_obj_tag(v___x_5155_) == 0)
{
goto v___jp_5149_;
}
else
{
v_a_5145_ = v_b_5143_;
goto v___jp_5144_;
}
}
}
v___jp_5144_:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5146_ = lean_unsigned_to_nat(1u);
v___x_5147_ = lean_nat_add(v_a_5142_, v___x_5146_);
lean_dec(v_a_5142_);
v_a_5142_ = v___x_5147_;
v_b_5143_ = v_a_5145_;
goto _start;
}
v___jp_5149_:
{
lean_object* v___x_5150_; lean_object* v___x_5151_; 
v___x_5150_ = lean_array_fget_borrowed(v_xs_5139_, v_a_5142_);
lean_inc(v___x_5150_);
v___x_5151_ = lean_array_push(v_b_5143_, v___x_5150_);
v_a_5145_ = v___x_5151_;
goto v___jp_5144_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5156_, lean_object* v_upperBound_5157_, lean_object* v_perm_5158_, lean_object* v_a_5159_, lean_object* v_b_5160_){
_start:
{
lean_object* v_res_5161_; 
v_res_5161_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5156_, v_upperBound_5157_, v_perm_5158_, v_a_5159_, v_b_5160_);
lean_dec_ref(v_perm_5158_);
lean_dec(v_upperBound_5157_);
lean_dec_ref(v_xs_5156_);
return v_res_5161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5162_, lean_object* v_xs_5163_){
_start:
{
lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v_ys_5166_; lean_object* v___x_5167_; 
v___x_5164_ = lean_array_get_size(v_xs_5163_);
v___x_5165_ = lean_unsigned_to_nat(0u);
v_ys_5166_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5167_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5163_, v___x_5164_, v_perm_5162_, v___x_5165_, v_ys_5166_);
return v___x_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5168_, lean_object* v_xs_5169_){
_start:
{
lean_object* v_res_5170_; 
v_res_5170_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5168_, v_xs_5169_);
lean_dec_ref(v_xs_5169_);
lean_dec_ref(v_perm_5168_);
return v_res_5170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5171_, lean_object* v_perm_5172_, lean_object* v_xs_5173_){
_start:
{
lean_object* v___x_5174_; 
v___x_5174_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5172_, v_xs_5173_);
return v___x_5174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5175_, lean_object* v_perm_5176_, lean_object* v_xs_5177_){
_start:
{
lean_object* v_res_5178_; 
v_res_5178_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5175_, v_perm_5176_, v_xs_5177_);
lean_dec_ref(v_xs_5177_);
lean_dec_ref(v_perm_5176_);
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5179_, lean_object* v_xs_5180_, lean_object* v_upperBound_5181_, lean_object* v_perm_5182_, lean_object* v_inst_5183_, lean_object* v_R_5184_, lean_object* v_a_5185_, lean_object* v_b_5186_, lean_object* v_c_5187_){
_start:
{
lean_object* v___x_5188_; 
v___x_5188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5180_, v_upperBound_5181_, v_perm_5182_, v_a_5185_, v_b_5186_);
return v___x_5188_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5189_, lean_object* v_xs_5190_, lean_object* v_upperBound_5191_, lean_object* v_perm_5192_, lean_object* v_inst_5193_, lean_object* v_R_5194_, lean_object* v_a_5195_, lean_object* v_b_5196_, lean_object* v_c_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5189_, v_xs_5190_, v_upperBound_5191_, v_perm_5192_, v_inst_5193_, v_R_5194_, v_a_5195_, v_b_5196_, v_c_5197_);
lean_dec_ref(v_perm_5192_);
lean_dec(v_upperBound_5191_);
lean_dec_ref(v_xs_5190_);
return v_res_5198_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(lean_object* v_msg_5199_){
_start:
{
lean_object* v___x_5200_; lean_object* v___x_5201_; 
v___x_5200_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5201_ = lean_panic_fn(v___x_5200_, v_msg_5199_);
return v___x_5201_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_00_u03b1_5202_, lean_object* v_msg_5203_){
_start:
{
lean_object* v___x_5204_; 
v___x_5204_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v_msg_5203_);
return v___x_5204_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_as_5205_, size_t v_i_5206_, size_t v_stop_5207_){
_start:
{
uint8_t v___x_5208_; 
v___x_5208_ = lean_usize_dec_eq(v_i_5206_, v_stop_5207_);
if (v___x_5208_ == 0)
{
uint8_t v___x_5209_; lean_object* v___x_5210_; 
v___x_5209_ = 1;
v___x_5210_ = lean_array_uget_borrowed(v_as_5205_, v_i_5206_);
if (lean_obj_tag(v___x_5210_) == 0)
{
if (v___x_5208_ == 0)
{
size_t v___x_5211_; size_t v___x_5212_; 
v___x_5211_ = ((size_t)1ULL);
v___x_5212_ = lean_usize_add(v_i_5206_, v___x_5211_);
v_i_5206_ = v___x_5212_;
goto _start;
}
else
{
return v___x_5209_;
}
}
else
{
return v___x_5209_;
}
}
else
{
uint8_t v___x_5214_; 
v___x_5214_ = 0;
return v___x_5214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___boxed(lean_object* v_as_5215_, lean_object* v_i_5216_, lean_object* v_stop_5217_){
_start:
{
size_t v_i_boxed_5218_; size_t v_stop_boxed_5219_; uint8_t v_res_5220_; lean_object* v_r_5221_; 
v_i_boxed_5218_ = lean_unbox_usize(v_i_5216_);
lean_dec(v_i_5216_);
v_stop_boxed_5219_ = lean_unbox_usize(v_stop_5217_);
lean_dec(v_stop_5217_);
v_res_5220_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v_as_5215_, v_i_boxed_5218_, v_stop_boxed_5219_);
lean_dec_ref(v_as_5215_);
v_r_5221_ = lean_box(v_res_5220_);
return v_r_5221_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; 
v___x_5224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5225_ = lean_unsigned_to_nat(12u);
v___x_5226_ = lean_unsigned_to_nat(433u);
v___x_5227_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5228_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5229_ = l_mkPanicMessageWithDecl(v___x_5228_, v___x_5227_, v___x_5226_, v___x_5225_, v___x_5224_);
return v___x_5229_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___x_5231_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5232_ = lean_unsigned_to_nat(10u);
v___x_5233_ = lean_unsigned_to_nat(425u);
v___x_5234_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5235_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5236_ = l_mkPanicMessageWithDecl(v___x_5235_, v___x_5234_, v___x_5233_, v___x_5232_, v___x_5231_);
return v___x_5236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5237_, lean_object* v_fixedArgs_5238_, lean_object* v_varyingArgs_5239_, lean_object* v_i_5240_, lean_object* v_j_5241_, lean_object* v_xs_5242_){
_start:
{
lean_object* v_lower_5244_; lean_object* v_upper_5245_; lean_object* v___y_5250_; lean_object* v___y_5251_; lean_object* v___y_5252_; lean_object* v_lower_5260_; lean_object* v_upper_5261_; lean_object* v___x_5269_; uint8_t v___x_5270_; 
v___x_5269_ = lean_array_get_size(v_perm_5237_);
v___x_5270_ = lean_nat_dec_lt(v_i_5240_, v___x_5269_);
if (v___x_5270_ == 0)
{
lean_object* v___x_5271_; lean_object* v___x_5272_; uint8_t v___x_5273_; 
lean_dec(v_i_5240_);
lean_dec_ref(v_perm_5237_);
v___x_5271_ = lean_unsigned_to_nat(0u);
v___x_5272_ = lean_array_get_size(v_varyingArgs_5239_);
v___x_5273_ = lean_nat_dec_le(v_j_5241_, v___x_5271_);
if (v___x_5273_ == 0)
{
v_lower_5244_ = v_j_5241_;
v_upper_5245_ = v___x_5272_;
goto v___jp_5243_;
}
else
{
lean_dec(v_j_5241_);
v_lower_5244_ = v___x_5271_;
v_upper_5245_ = v___x_5272_;
goto v___jp_5243_;
}
}
else
{
lean_object* v___x_5274_; 
v___x_5274_ = lean_array_fget_borrowed(v_perm_5237_, v_i_5240_);
if (lean_obj_tag(v___x_5274_) == 1)
{
lean_object* v_val_5275_; lean_object* v___x_5276_; uint8_t v___x_5277_; 
v_val_5275_ = lean_ctor_get(v___x_5274_, 0);
v___x_5276_ = lean_array_get_size(v_fixedArgs_5238_);
v___x_5277_ = lean_nat_dec_lt(v_val_5275_, v___x_5276_);
if (v___x_5277_ == 0)
{
lean_object* v___x_5278_; lean_object* v___x_5279_; 
lean_dec_ref(v_xs_5242_);
lean_dec(v_j_5241_);
lean_dec(v_i_5240_);
lean_dec_ref(v_varyingArgs_5239_);
lean_dec_ref(v_perm_5237_);
v___x_5278_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5279_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5278_);
return v___x_5279_;
}
else
{
lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v___x_5280_ = lean_unsigned_to_nat(1u);
v___x_5281_ = lean_nat_add(v_i_5240_, v___x_5280_);
lean_dec(v_i_5240_);
v___x_5282_ = lean_array_fget_borrowed(v_fixedArgs_5238_, v_val_5275_);
lean_inc(v___x_5282_);
v___x_5283_ = lean_array_push(v_xs_5242_, v___x_5282_);
v_i_5240_ = v___x_5281_;
v_xs_5242_ = v___x_5283_;
goto _start;
}
}
else
{
lean_object* v___x_5285_; uint8_t v___x_5286_; 
v___x_5285_ = lean_array_get_size(v_varyingArgs_5239_);
v___x_5286_ = lean_nat_dec_lt(v_j_5241_, v___x_5285_);
if (v___x_5286_ == 0)
{
lean_object* v___x_5287_; uint8_t v___x_5288_; 
lean_dec(v_j_5241_);
lean_dec_ref(v_varyingArgs_5239_);
v___x_5287_ = lean_unsigned_to_nat(0u);
v___x_5288_ = lean_nat_dec_le(v_i_5240_, v___x_5287_);
if (v___x_5288_ == 0)
{
v_lower_5260_ = v_i_5240_;
v_upper_5261_ = v___x_5269_;
goto v___jp_5259_;
}
else
{
lean_dec(v_i_5240_);
v_lower_5260_ = v___x_5287_;
v_upper_5261_ = v___x_5269_;
goto v___jp_5259_;
}
}
else
{
lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
v___x_5289_ = lean_unsigned_to_nat(1u);
v___x_5290_ = lean_nat_add(v_i_5240_, v___x_5289_);
lean_dec(v_i_5240_);
v___x_5291_ = lean_nat_add(v_j_5241_, v___x_5289_);
v___x_5292_ = lean_array_fget_borrowed(v_varyingArgs_5239_, v_j_5241_);
lean_dec(v_j_5241_);
lean_inc(v___x_5292_);
v___x_5293_ = lean_array_push(v_xs_5242_, v___x_5292_);
v_i_5240_ = v___x_5290_;
v_j_5241_ = v___x_5291_;
v_xs_5242_ = v___x_5293_;
goto _start;
}
}
}
v___jp_5243_:
{
lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; 
v___x_5246_ = l_Array_toSubarray___redArg(v_varyingArgs_5239_, v_lower_5244_, v_upper_5245_);
v___x_5247_ = l_Subarray_copy___redArg(v___x_5246_);
v___x_5248_ = l_Array_append___redArg(v_xs_5242_, v___x_5247_);
lean_dec_ref(v___x_5247_);
return v___x_5248_;
}
v___jp_5249_:
{
uint8_t v___x_5253_; 
v___x_5253_ = lean_nat_dec_lt(v___y_5251_, v___y_5252_);
if (v___x_5253_ == 0)
{
lean_dec(v___y_5252_);
lean_dec(v___y_5251_);
lean_dec_ref(v___y_5250_);
return v_xs_5242_;
}
else
{
size_t v___x_5254_; size_t v___x_5255_; uint8_t v___x_5256_; 
v___x_5254_ = lean_usize_of_nat(v___y_5251_);
lean_dec(v___y_5251_);
v___x_5255_ = lean_usize_of_nat(v___y_5252_);
lean_dec(v___y_5252_);
v___x_5256_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v___y_5250_, v___x_5254_, v___x_5255_);
lean_dec_ref(v___y_5250_);
if (v___x_5256_ == 0)
{
return v_xs_5242_;
}
else
{
lean_object* v___x_5257_; lean_object* v___x_5258_; 
lean_dec_ref(v_xs_5242_);
v___x_5257_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5258_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5257_);
return v___x_5258_;
}
}
}
v___jp_5259_:
{
lean_object* v___x_5262_; lean_object* v_array_5263_; lean_object* v_start_5264_; lean_object* v_stop_5265_; uint8_t v___x_5266_; 
v___x_5262_ = l_Array_toSubarray___redArg(v_perm_5237_, v_lower_5260_, v_upper_5261_);
v_array_5263_ = lean_ctor_get(v___x_5262_, 0);
lean_inc_ref(v_array_5263_);
v_start_5264_ = lean_ctor_get(v___x_5262_, 1);
lean_inc(v_start_5264_);
v_stop_5265_ = lean_ctor_get(v___x_5262_, 2);
lean_inc(v_stop_5265_);
lean_dec_ref(v___x_5262_);
v___x_5266_ = lean_nat_dec_lt(v_start_5264_, v_stop_5265_);
if (v___x_5266_ == 0)
{
lean_dec(v_stop_5265_);
lean_dec(v_start_5264_);
lean_dec_ref(v_array_5263_);
return v_xs_5242_;
}
else
{
lean_object* v___x_5267_; uint8_t v___x_5268_; 
v___x_5267_ = lean_array_get_size(v_array_5263_);
v___x_5268_ = lean_nat_dec_le(v_stop_5265_, v___x_5267_);
if (v___x_5268_ == 0)
{
lean_dec(v_stop_5265_);
v___y_5250_ = v_array_5263_;
v___y_5251_ = v_start_5264_;
v___y_5252_ = v___x_5267_;
goto v___jp_5249_;
}
else
{
v___y_5250_ = v_array_5263_;
v___y_5251_ = v_start_5264_;
v___y_5252_ = v_stop_5265_;
goto v___jp_5249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5295_, lean_object* v_fixedArgs_5296_, lean_object* v_varyingArgs_5297_, lean_object* v_i_5298_, lean_object* v_j_5299_, lean_object* v_xs_5300_){
_start:
{
lean_object* v_res_5301_; 
v_res_5301_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5295_, v_fixedArgs_5296_, v_varyingArgs_5297_, v_i_5298_, v_j_5299_, v_xs_5300_);
lean_dec_ref(v_fixedArgs_5296_);
return v_res_5301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5302_, lean_object* v_perm_5303_, lean_object* v_fixedArgs_5304_, lean_object* v_varyingArgs_5305_, lean_object* v_i_5306_, lean_object* v_j_5307_, lean_object* v_xs_5308_){
_start:
{
lean_object* v___x_5309_; 
v___x_5309_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5303_, v_fixedArgs_5304_, v_varyingArgs_5305_, v_i_5306_, v_j_5307_, v_xs_5308_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5310_, lean_object* v_perm_5311_, lean_object* v_fixedArgs_5312_, lean_object* v_varyingArgs_5313_, lean_object* v_i_5314_, lean_object* v_j_5315_, lean_object* v_xs_5316_){
_start:
{
lean_object* v_res_5317_; 
v_res_5317_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5310_, v_perm_5311_, v_fixedArgs_5312_, v_varyingArgs_5313_, v_i_5314_, v_j_5315_, v_xs_5316_);
lean_dec_ref(v_fixedArgs_5312_);
return v_res_5317_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; 
v___x_5320_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5321_ = lean_unsigned_to_nat(2u);
v___x_5322_ = lean_unsigned_to_nat(416u);
v___x_5323_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5324_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5325_ = l_mkPanicMessageWithDecl(v___x_5324_, v___x_5323_, v___x_5322_, v___x_5321_, v___x_5320_);
return v___x_5325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5326_, lean_object* v_fixedArgs_5327_, lean_object* v_varyingArgs_5328_){
_start:
{
lean_object* v___x_5329_; lean_object* v___x_5330_; uint8_t v___x_5331_; 
v___x_5329_ = lean_array_get_size(v_fixedArgs_5327_);
v___x_5330_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5326_);
v___x_5331_ = lean_nat_dec_eq(v___x_5329_, v___x_5330_);
lean_dec(v___x_5330_);
if (v___x_5331_ == 0)
{
lean_object* v___x_5332_; lean_object* v___x_5333_; 
lean_dec_ref(v_varyingArgs_5328_);
lean_dec_ref(v_perm_5326_);
v___x_5332_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5333_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5332_);
return v___x_5333_;
}
else
{
lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5334_ = lean_unsigned_to_nat(0u);
v___x_5335_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5336_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5326_, v_fixedArgs_5327_, v_varyingArgs_5328_, v___x_5334_, v___x_5334_, v___x_5335_);
return v___x_5336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5337_, lean_object* v_fixedArgs_5338_, lean_object* v_varyingArgs_5339_){
_start:
{
lean_object* v_res_5340_; 
v_res_5340_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5337_, v_fixedArgs_5338_, v_varyingArgs_5339_);
lean_dec_ref(v_fixedArgs_5338_);
return v_res_5340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5341_, lean_object* v_perm_5342_, lean_object* v_fixedArgs_5343_, lean_object* v_varyingArgs_5344_){
_start:
{
lean_object* v___x_5345_; 
v___x_5345_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5342_, v_fixedArgs_5343_, v_varyingArgs_5344_);
return v___x_5345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5346_, lean_object* v_perm_5347_, lean_object* v_fixedArgs_5348_, lean_object* v_varyingArgs_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5346_, v_perm_5347_, v_fixedArgs_5348_, v_varyingArgs_5349_);
lean_dec_ref(v_fixedArgs_5348_);
return v_res_5350_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5351_, lean_object* v_x_5352_){
_start:
{
if (lean_obj_tag(v_x_5351_) == 0)
{
if (lean_obj_tag(v_x_5352_) == 0)
{
uint8_t v___x_5353_; 
v___x_5353_ = 1;
return v___x_5353_;
}
else
{
uint8_t v___x_5354_; 
v___x_5354_ = 0;
return v___x_5354_;
}
}
else
{
if (lean_obj_tag(v_x_5352_) == 0)
{
uint8_t v___x_5355_; 
v___x_5355_ = 0;
return v___x_5355_;
}
else
{
lean_object* v_val_5356_; lean_object* v_val_5357_; uint8_t v___x_5358_; 
v_val_5356_ = lean_ctor_get(v_x_5351_, 0);
v_val_5357_ = lean_ctor_get(v_x_5352_, 0);
v___x_5358_ = lean_nat_dec_eq(v_val_5356_, v_val_5357_);
return v___x_5358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5359_, lean_object* v_x_5360_){
_start:
{
uint8_t v_res_5361_; lean_object* v_r_5362_; 
v_res_5361_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5359_, v_x_5360_);
lean_dec(v_x_5360_);
lean_dec(v_x_5359_);
v_r_5362_ = lean_box(v_res_5361_);
return v_r_5362_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5363_, lean_object* v_ys_5364_, lean_object* v_x_5365_){
_start:
{
lean_object* v_zero_5366_; uint8_t v_isZero_5367_; 
v_zero_5366_ = lean_unsigned_to_nat(0u);
v_isZero_5367_ = lean_nat_dec_eq(v_x_5365_, v_zero_5366_);
if (v_isZero_5367_ == 1)
{
lean_dec(v_x_5365_);
return v_isZero_5367_;
}
else
{
lean_object* v_one_5368_; lean_object* v_n_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; uint8_t v___x_5372_; 
v_one_5368_ = lean_unsigned_to_nat(1u);
v_n_5369_ = lean_nat_sub(v_x_5365_, v_one_5368_);
lean_dec(v_x_5365_);
v___x_5370_ = lean_array_fget_borrowed(v_xs_5363_, v_n_5369_);
v___x_5371_ = lean_array_fget_borrowed(v_ys_5364_, v_n_5369_);
v___x_5372_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5370_, v___x_5371_);
if (v___x_5372_ == 0)
{
lean_dec(v_n_5369_);
return v___x_5372_;
}
else
{
v_x_5365_ = v_n_5369_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5374_, lean_object* v_ys_5375_, lean_object* v_x_5376_){
_start:
{
uint8_t v_res_5377_; lean_object* v_r_5378_; 
v_res_5377_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5374_, v_ys_5375_, v_x_5376_);
lean_dec_ref(v_ys_5375_);
lean_dec_ref(v_xs_5374_);
v_r_5378_ = lean_box(v_res_5377_);
return v_r_5378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5379_, size_t v_i_5380_, lean_object* v_bs_5381_){
_start:
{
uint8_t v___x_5382_; 
v___x_5382_ = lean_usize_dec_lt(v_i_5380_, v_sz_5379_);
if (v___x_5382_ == 0)
{
return v_bs_5381_;
}
else
{
lean_object* v_v_5383_; lean_object* v___x_5384_; lean_object* v_bs_x27_5385_; lean_object* v___x_5386_; size_t v___x_5387_; size_t v___x_5388_; lean_object* v___x_5389_; 
v_v_5383_ = lean_array_uget(v_bs_5381_, v_i_5380_);
v___x_5384_ = lean_unsigned_to_nat(0u);
v_bs_x27_5385_ = lean_array_uset(v_bs_5381_, v_i_5380_, v___x_5384_);
v___x_5386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5386_, 0, v_v_5383_);
v___x_5387_ = ((size_t)1ULL);
v___x_5388_ = lean_usize_add(v_i_5380_, v___x_5387_);
v___x_5389_ = lean_array_uset(v_bs_x27_5385_, v_i_5380_, v___x_5386_);
v_i_5380_ = v___x_5388_;
v_bs_5381_ = v___x_5389_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5391_, lean_object* v_i_5392_, lean_object* v_bs_5393_){
_start:
{
size_t v_sz_boxed_5394_; size_t v_i_boxed_5395_; lean_object* v_res_5396_; 
v_sz_boxed_5394_ = lean_unbox_usize(v_sz_5391_);
lean_dec(v_sz_5391_);
v_i_boxed_5395_ = lean_unbox_usize(v_i_5392_);
lean_dec(v_i_5392_);
v_res_5396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5394_, v_i_boxed_5395_, v_bs_5393_);
return v_res_5396_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5397_, lean_object* v_as_5398_, size_t v_i_5399_, size_t v_stop_5400_){
_start:
{
uint8_t v___x_5401_; 
v___x_5401_ = lean_usize_dec_eq(v_i_5399_, v_stop_5400_);
if (v___x_5401_ == 0)
{
lean_object* v_numFixed_5402_; uint8_t v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; size_t v_sz_5406_; size_t v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; uint8_t v___x_5415_; 
v_numFixed_5402_ = lean_ctor_get(v_fixedParamPerms_5397_, 0);
v___x_5403_ = 1;
v___x_5404_ = lean_array_uget_borrowed(v_as_5398_, v_i_5399_);
lean_inc(v_numFixed_5402_);
v___x_5405_ = l_Array_range(v_numFixed_5402_);
v_sz_5406_ = lean_array_size(v___x_5405_);
v___x_5407_ = ((size_t)0ULL);
v___x_5408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5406_, v___x_5407_, v___x_5405_);
v___x_5409_ = lean_array_get_size(v___x_5404_);
v___x_5410_ = lean_nat_sub(v___x_5409_, v_numFixed_5402_);
v___x_5411_ = lean_box(0);
v___x_5412_ = lean_mk_array(v___x_5410_, v___x_5411_);
v___x_5413_ = l_Array_append___redArg(v___x_5408_, v___x_5412_);
lean_dec_ref(v___x_5412_);
v___x_5414_ = lean_array_get_size(v___x_5413_);
v___x_5415_ = lean_nat_dec_eq(v___x_5409_, v___x_5414_);
if (v___x_5415_ == 0)
{
lean_dec_ref(v___x_5413_);
lean_dec_ref(v_fixedParamPerms_5397_);
return v___x_5403_;
}
else
{
uint8_t v___x_5416_; 
v___x_5416_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5404_, v___x_5413_, v___x_5409_);
lean_dec_ref(v___x_5413_);
if (v___x_5416_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5397_);
return v___x_5403_;
}
else
{
if (v___x_5401_ == 0)
{
size_t v___x_5417_; size_t v___x_5418_; 
v___x_5417_ = ((size_t)1ULL);
v___x_5418_ = lean_usize_add(v_i_5399_, v___x_5417_);
v_i_5399_ = v___x_5418_;
goto _start;
}
else
{
lean_dec_ref(v_fixedParamPerms_5397_);
return v___x_5403_;
}
}
}
}
else
{
uint8_t v___x_5420_; 
lean_dec_ref(v_fixedParamPerms_5397_);
v___x_5420_ = 0;
return v___x_5420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5421_, lean_object* v_as_5422_, lean_object* v_i_5423_, lean_object* v_stop_5424_){
_start:
{
size_t v_i_boxed_5425_; size_t v_stop_boxed_5426_; uint8_t v_res_5427_; lean_object* v_r_5428_; 
v_i_boxed_5425_ = lean_unbox_usize(v_i_5423_);
lean_dec(v_i_5423_);
v_stop_boxed_5426_ = lean_unbox_usize(v_stop_5424_);
lean_dec(v_stop_5424_);
v_res_5427_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5421_, v_as_5422_, v_i_boxed_5425_, v_stop_boxed_5426_);
lean_dec_ref(v_as_5422_);
v_r_5428_ = lean_box(v_res_5427_);
return v_r_5428_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5429_){
_start:
{
lean_object* v_perms_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; uint8_t v___x_5433_; 
v_perms_5430_ = lean_ctor_get(v_fixedParamPerms_5429_, 1);
lean_inc_ref(v_perms_5430_);
v___x_5431_ = lean_unsigned_to_nat(0u);
v___x_5432_ = lean_array_get_size(v_perms_5430_);
v___x_5433_ = lean_nat_dec_lt(v___x_5431_, v___x_5432_);
if (v___x_5433_ == 0)
{
uint8_t v___x_5434_; 
lean_dec_ref(v_perms_5430_);
lean_dec_ref(v_fixedParamPerms_5429_);
v___x_5434_ = 1;
return v___x_5434_;
}
else
{
if (v___x_5433_ == 0)
{
lean_dec_ref(v_perms_5430_);
lean_dec_ref(v_fixedParamPerms_5429_);
return v___x_5433_;
}
else
{
size_t v___x_5435_; size_t v___x_5436_; uint8_t v___x_5437_; 
v___x_5435_ = ((size_t)0ULL);
v___x_5436_ = lean_usize_of_nat(v___x_5432_);
v___x_5437_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5429_, v_perms_5430_, v___x_5435_, v___x_5436_);
lean_dec_ref(v_perms_5430_);
if (v___x_5437_ == 0)
{
return v___x_5433_;
}
else
{
uint8_t v___x_5438_; 
v___x_5438_ = 0;
return v___x_5438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5439_){
_start:
{
uint8_t v_res_5440_; lean_object* v_r_5441_; 
v_res_5440_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5439_);
v_r_5441_ = lean_box(v_res_5440_);
return v_r_5441_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5442_, lean_object* v_ys_5443_, lean_object* v_hsz_5444_, lean_object* v_x_5445_, lean_object* v_x_5446_){
_start:
{
uint8_t v___x_5447_; 
v___x_5447_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5442_, v_ys_5443_, v_x_5445_);
return v___x_5447_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5448_, lean_object* v_ys_5449_, lean_object* v_hsz_5450_, lean_object* v_x_5451_, lean_object* v_x_5452_){
_start:
{
uint8_t v_res_5453_; lean_object* v_r_5454_; 
v_res_5453_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5448_, v_ys_5449_, v_hsz_5450_, v_x_5451_, v_x_5452_);
lean_dec_ref(v_ys_5449_);
lean_dec_ref(v_xs_5448_);
v_r_5454_ = lean_box(v_res_5453_);
return v_r_5454_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5455_; 
v___x_5455_ = l_Array_instInhabited(lean_box(0));
return v___x_5455_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5456_){
_start:
{
lean_object* v___f_5457_; lean_object* v___f_5458_; lean_object* v___f_5459_; lean_object* v___f_5460_; lean_object* v___f_5461_; lean_object* v___f_5462_; lean_object* v___f_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; 
v___f_5457_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5458_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5459_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5460_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5461_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5462_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5463_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5464_, 0, v___f_5457_);
lean_ctor_set(v___x_5464_, 1, v___f_5458_);
v___x_5465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5465_, 0, v___x_5464_);
lean_ctor_set(v___x_5465_, 1, v___f_5459_);
lean_ctor_set(v___x_5465_, 2, v___f_5460_);
lean_ctor_set(v___x_5465_, 3, v___f_5461_);
lean_ctor_set(v___x_5465_, 4, v___f_5462_);
v___x_5466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5466_, 0, v___x_5465_);
lean_ctor_set(v___x_5466_, 1, v___f_5463_);
v___x_5467_ = l_Lean_Elab_instInhabitedFixedParamPerms_default;
v___x_5468_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5469_, 0, v___x_5468_);
lean_ctor_set(v___x_5469_, 1, v___x_5468_);
v___x_5470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5470_, 0, v___x_5467_);
lean_ctor_set(v___x_5470_, 1, v___x_5469_);
v___x_5471_ = l_instInhabitedOfMonad___redArg(v___x_5466_, v___x_5470_);
v___x_5472_ = lean_panic_fn(v___x_5471_, v_msg_5456_);
return v___x_5472_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5473_; 
v___x_5473_ = l_Array_instInhabited(lean_box(0));
return v___x_5473_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5474_){
_start:
{
lean_object* v___f_5475_; lean_object* v___f_5476_; lean_object* v___f_5477_; lean_object* v___f_5478_; lean_object* v___f_5479_; lean_object* v___f_5480_; lean_object* v___f_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; 
v___f_5475_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5476_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5477_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5478_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5479_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5480_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5481_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5482_, 0, v___f_5475_);
lean_ctor_set(v___x_5482_, 1, v___f_5476_);
v___x_5483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5483_, 0, v___x_5482_);
lean_ctor_set(v___x_5483_, 1, v___f_5477_);
lean_ctor_set(v___x_5483_, 2, v___f_5478_);
lean_ctor_set(v___x_5483_, 3, v___f_5479_);
lean_ctor_set(v___x_5483_, 4, v___f_5480_);
v___x_5484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5484_, 0, v___x_5483_);
lean_ctor_set(v___x_5484_, 1, v___f_5481_);
v___x_5485_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5486_, 0, v___x_5485_);
v___x_5487_ = l_instInhabitedOfMonad___redArg(v___x_5484_, v___x_5486_);
v___x_5488_ = lean_panic_fn(v___x_5487_, v_msg_5474_);
return v___x_5488_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5489_, lean_object* v_a_5490_, lean_object* v_b_5491_){
_start:
{
lean_object* v_a_5493_; uint8_t v___x_5497_; 
v___x_5497_ = lean_nat_dec_lt(v_a_5490_, v_upperBound_5489_);
if (v___x_5497_ == 0)
{
lean_dec(v_a_5490_);
return v_b_5491_;
}
else
{
lean_object* v_snd_5498_; lean_object* v_snd_5499_; lean_object* v_snd_5500_; lean_object* v_snd_5501_; lean_object* v_fst_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5614_; 
v_snd_5498_ = lean_ctor_get(v_b_5491_, 1);
lean_inc(v_snd_5498_);
v_snd_5499_ = lean_ctor_get(v_snd_5498_, 1);
lean_inc(v_snd_5499_);
v_snd_5500_ = lean_ctor_get(v_snd_5499_, 1);
lean_inc(v_snd_5500_);
v_snd_5501_ = lean_ctor_get(v_snd_5500_, 1);
lean_inc(v_snd_5501_);
v_fst_5502_ = lean_ctor_get(v_b_5491_, 0);
v_isSharedCheck_5614_ = !lean_is_exclusive(v_b_5491_);
if (v_isSharedCheck_5614_ == 0)
{
lean_object* v_unused_5615_; 
v_unused_5615_ = lean_ctor_get(v_b_5491_, 1);
lean_dec(v_unused_5615_);
v___x_5504_ = v_b_5491_;
v_isShared_5505_ = v_isSharedCheck_5614_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_fst_5502_);
lean_dec(v_b_5491_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5614_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v_fst_5506_; lean_object* v___x_5508_; uint8_t v_isShared_5509_; uint8_t v_isSharedCheck_5612_; 
v_fst_5506_ = lean_ctor_get(v_snd_5498_, 0);
v_isSharedCheck_5612_ = !lean_is_exclusive(v_snd_5498_);
if (v_isSharedCheck_5612_ == 0)
{
lean_object* v_unused_5613_; 
v_unused_5613_ = lean_ctor_get(v_snd_5498_, 1);
lean_dec(v_unused_5613_);
v___x_5508_ = v_snd_5498_;
v_isShared_5509_ = v_isSharedCheck_5612_;
goto v_resetjp_5507_;
}
else
{
lean_inc(v_fst_5506_);
lean_dec(v_snd_5498_);
v___x_5508_ = lean_box(0);
v_isShared_5509_ = v_isSharedCheck_5612_;
goto v_resetjp_5507_;
}
v_resetjp_5507_:
{
lean_object* v_fst_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5610_; 
v_fst_5510_ = lean_ctor_get(v_snd_5499_, 0);
v_isSharedCheck_5610_ = !lean_is_exclusive(v_snd_5499_);
if (v_isSharedCheck_5610_ == 0)
{
lean_object* v_unused_5611_; 
v_unused_5611_ = lean_ctor_get(v_snd_5499_, 1);
lean_dec(v_unused_5611_);
v___x_5512_ = v_snd_5499_;
v_isShared_5513_ = v_isSharedCheck_5610_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_fst_5510_);
lean_dec(v_snd_5499_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5610_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v_fst_5514_; lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5608_; 
v_fst_5514_ = lean_ctor_get(v_snd_5500_, 0);
v_isSharedCheck_5608_ = !lean_is_exclusive(v_snd_5500_);
if (v_isSharedCheck_5608_ == 0)
{
lean_object* v_unused_5609_; 
v_unused_5609_ = lean_ctor_get(v_snd_5500_, 1);
lean_dec(v_unused_5609_);
v___x_5516_ = v_snd_5500_;
v_isShared_5517_ = v_isSharedCheck_5608_;
goto v_resetjp_5515_;
}
else
{
lean_inc(v_fst_5514_);
lean_dec(v_snd_5500_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5608_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
lean_object* v_array_5518_; lean_object* v_start_5519_; lean_object* v_stop_5520_; uint8_t v___x_5521_; 
v_array_5518_ = lean_ctor_get(v_snd_5501_, 0);
v_start_5519_ = lean_ctor_get(v_snd_5501_, 1);
v_stop_5520_ = lean_ctor_get(v_snd_5501_, 2);
v___x_5521_ = lean_nat_dec_lt(v_start_5519_, v_stop_5520_);
if (v___x_5521_ == 0)
{
lean_object* v___x_5523_; 
lean_dec(v_a_5490_);
if (v_isShared_5517_ == 0)
{
v___x_5523_ = v___x_5516_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_fst_5514_);
lean_ctor_set(v_reuseFailAlloc_5533_, 1, v_snd_5501_);
v___x_5523_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
lean_object* v___x_5525_; 
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 1, v___x_5523_);
v___x_5525_ = v___x_5512_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_fst_5510_);
lean_ctor_set(v_reuseFailAlloc_5532_, 1, v___x_5523_);
v___x_5525_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
lean_object* v___x_5527_; 
if (v_isShared_5509_ == 0)
{
lean_ctor_set(v___x_5508_, 1, v___x_5525_);
v___x_5527_ = v___x_5508_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v_fst_5506_);
lean_ctor_set(v_reuseFailAlloc_5531_, 1, v___x_5525_);
v___x_5527_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
lean_object* v___x_5529_; 
if (v_isShared_5505_ == 0)
{
lean_ctor_set(v___x_5504_, 1, v___x_5527_);
v___x_5529_ = v___x_5504_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_fst_5502_);
lean_ctor_set(v_reuseFailAlloc_5530_, 1, v___x_5527_);
v___x_5529_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
return v___x_5529_;
}
}
}
}
}
else
{
lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5604_; 
lean_inc(v_stop_5520_);
lean_inc(v_start_5519_);
lean_inc_ref(v_array_5518_);
v_isSharedCheck_5604_ = !lean_is_exclusive(v_snd_5501_);
if (v_isSharedCheck_5604_ == 0)
{
lean_object* v_unused_5605_; lean_object* v_unused_5606_; lean_object* v_unused_5607_; 
v_unused_5605_ = lean_ctor_get(v_snd_5501_, 2);
lean_dec(v_unused_5605_);
v_unused_5606_ = lean_ctor_get(v_snd_5501_, 1);
lean_dec(v_unused_5606_);
v_unused_5607_ = lean_ctor_get(v_snd_5501_, 0);
lean_dec(v_unused_5607_);
v___x_5535_ = v_snd_5501_;
v_isShared_5536_ = v_isSharedCheck_5604_;
goto v_resetjp_5534_;
}
else
{
lean_dec(v_snd_5501_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5604_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v_array_5537_; lean_object* v_start_5538_; lean_object* v_stop_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5544_; 
v_array_5537_ = lean_ctor_get(v_fst_5514_, 0);
v_start_5538_ = lean_ctor_get(v_fst_5514_, 1);
v_stop_5539_ = lean_ctor_get(v_fst_5514_, 2);
v___x_5540_ = lean_array_fget(v_array_5518_, v_start_5519_);
v___x_5541_ = lean_unsigned_to_nat(1u);
v___x_5542_ = lean_nat_add(v_start_5519_, v___x_5541_);
lean_dec(v_start_5519_);
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 1, v___x_5542_);
v___x_5544_ = v___x_5535_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_array_5518_);
lean_ctor_set(v_reuseFailAlloc_5603_, 1, v___x_5542_);
lean_ctor_set(v_reuseFailAlloc_5603_, 2, v_stop_5520_);
v___x_5544_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
uint8_t v___x_5545_; 
v___x_5545_ = lean_nat_dec_lt(v_start_5538_, v_stop_5539_);
if (v___x_5545_ == 0)
{
lean_object* v___x_5547_; 
lean_dec(v___x_5540_);
lean_dec(v_a_5490_);
if (v_isShared_5517_ == 0)
{
lean_ctor_set(v___x_5516_, 1, v___x_5544_);
v___x_5547_ = v___x_5516_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_fst_5514_);
lean_ctor_set(v_reuseFailAlloc_5557_, 1, v___x_5544_);
v___x_5547_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
lean_object* v___x_5549_; 
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 1, v___x_5547_);
v___x_5549_ = v___x_5512_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v_fst_5510_);
lean_ctor_set(v_reuseFailAlloc_5556_, 1, v___x_5547_);
v___x_5549_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
lean_object* v___x_5551_; 
if (v_isShared_5509_ == 0)
{
lean_ctor_set(v___x_5508_, 1, v___x_5549_);
v___x_5551_ = v___x_5508_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v_fst_5506_);
lean_ctor_set(v_reuseFailAlloc_5555_, 1, v___x_5549_);
v___x_5551_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
lean_object* v___x_5553_; 
if (v_isShared_5505_ == 0)
{
lean_ctor_set(v___x_5504_, 1, v___x_5551_);
v___x_5553_ = v___x_5504_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v_fst_5502_);
lean_ctor_set(v_reuseFailAlloc_5554_, 1, v___x_5551_);
v___x_5553_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
return v___x_5553_;
}
}
}
}
}
else
{
lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5599_; 
lean_inc(v_stop_5539_);
lean_inc(v_start_5538_);
lean_inc_ref(v_array_5537_);
v_isSharedCheck_5599_ = !lean_is_exclusive(v_fst_5514_);
if (v_isSharedCheck_5599_ == 0)
{
lean_object* v_unused_5600_; lean_object* v_unused_5601_; lean_object* v_unused_5602_; 
v_unused_5600_ = lean_ctor_get(v_fst_5514_, 2);
lean_dec(v_unused_5600_);
v_unused_5601_ = lean_ctor_get(v_fst_5514_, 1);
lean_dec(v_unused_5601_);
v_unused_5602_ = lean_ctor_get(v_fst_5514_, 0);
lean_dec(v_unused_5602_);
v___x_5559_ = v_fst_5514_;
v_isShared_5560_ = v_isSharedCheck_5599_;
goto v_resetjp_5558_;
}
else
{
lean_dec(v_fst_5514_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5599_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5564_; 
v___x_5561_ = lean_array_fget(v_array_5537_, v_start_5538_);
v___x_5562_ = lean_nat_add(v_start_5538_, v___x_5541_);
lean_dec(v_start_5538_);
if (v_isShared_5560_ == 0)
{
lean_ctor_set(v___x_5559_, 1, v___x_5562_);
v___x_5564_ = v___x_5559_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_array_5537_);
lean_ctor_set(v_reuseFailAlloc_5598_, 1, v___x_5562_);
lean_ctor_set(v_reuseFailAlloc_5598_, 2, v_stop_5539_);
v___x_5564_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
uint8_t v___x_5565_; 
v___x_5565_ = lean_unbox(v___x_5561_);
lean_dec(v___x_5561_);
if (v___x_5565_ == 0)
{
lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5571_; 
v___x_5566_ = lean_array_get_size(v_fst_5510_);
v___x_5567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5567_, 0, v___x_5566_);
v___x_5568_ = lean_array_push(v_fst_5502_, v___x_5567_);
v___x_5569_ = lean_array_push(v_fst_5510_, v___x_5540_);
if (v_isShared_5517_ == 0)
{
lean_ctor_set(v___x_5516_, 1, v___x_5544_);
lean_ctor_set(v___x_5516_, 0, v___x_5564_);
v___x_5571_ = v___x_5516_;
goto v_reusejp_5570_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v___x_5564_);
lean_ctor_set(v_reuseFailAlloc_5581_, 1, v___x_5544_);
v___x_5571_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5570_;
}
v_reusejp_5570_:
{
lean_object* v___x_5573_; 
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 1, v___x_5571_);
lean_ctor_set(v___x_5512_, 0, v___x_5569_);
v___x_5573_ = v___x_5512_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v___x_5569_);
lean_ctor_set(v_reuseFailAlloc_5580_, 1, v___x_5571_);
v___x_5573_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
lean_object* v___x_5575_; 
if (v_isShared_5509_ == 0)
{
lean_ctor_set(v___x_5508_, 1, v___x_5573_);
v___x_5575_ = v___x_5508_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_fst_5506_);
lean_ctor_set(v_reuseFailAlloc_5579_, 1, v___x_5573_);
v___x_5575_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
lean_object* v___x_5577_; 
if (v_isShared_5505_ == 0)
{
lean_ctor_set(v___x_5504_, 1, v___x_5575_);
lean_ctor_set(v___x_5504_, 0, v___x_5568_);
v___x_5577_ = v___x_5504_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5568_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v___x_5575_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
v_a_5493_ = v___x_5577_;
goto v___jp_5492_;
}
}
}
}
}
else
{
lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5587_; 
v___x_5582_ = lean_box(0);
v___x_5583_ = lean_array_push(v_fst_5502_, v___x_5582_);
v___x_5584_ = l_Lean_Expr_fvarId_x21(v___x_5540_);
lean_dec(v___x_5540_);
v___x_5585_ = lean_array_push(v_fst_5506_, v___x_5584_);
if (v_isShared_5517_ == 0)
{
lean_ctor_set(v___x_5516_, 1, v___x_5544_);
lean_ctor_set(v___x_5516_, 0, v___x_5564_);
v___x_5587_ = v___x_5516_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v___x_5564_);
lean_ctor_set(v_reuseFailAlloc_5597_, 1, v___x_5544_);
v___x_5587_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
lean_object* v___x_5589_; 
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 1, v___x_5587_);
v___x_5589_ = v___x_5512_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_fst_5510_);
lean_ctor_set(v_reuseFailAlloc_5596_, 1, v___x_5587_);
v___x_5589_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
lean_object* v___x_5591_; 
if (v_isShared_5509_ == 0)
{
lean_ctor_set(v___x_5508_, 1, v___x_5589_);
lean_ctor_set(v___x_5508_, 0, v___x_5585_);
v___x_5591_ = v___x_5508_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v___x_5585_);
lean_ctor_set(v_reuseFailAlloc_5595_, 1, v___x_5589_);
v___x_5591_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
lean_object* v___x_5593_; 
if (v_isShared_5505_ == 0)
{
lean_ctor_set(v___x_5504_, 1, v___x_5591_);
lean_ctor_set(v___x_5504_, 0, v___x_5583_);
v___x_5593_ = v___x_5504_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5583_);
lean_ctor_set(v_reuseFailAlloc_5594_, 1, v___x_5591_);
v___x_5593_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
v_a_5493_ = v___x_5593_;
goto v___jp_5492_;
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
v___jp_5492_:
{
lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5494_ = lean_unsigned_to_nat(1u);
v___x_5495_ = lean_nat_add(v_a_5490_, v___x_5494_);
lean_dec(v_a_5490_);
v_a_5490_ = v___x_5495_;
v_b_5491_ = v_a_5493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5616_, lean_object* v_a_5617_, lean_object* v_b_5618_){
_start:
{
lean_object* v_res_5619_; 
v_res_5619_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5616_, v_a_5617_, v_b_5618_);
lean_dec(v_upperBound_5616_);
return v_res_5619_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5620_, size_t v_i_5621_, size_t v_stop_5622_){
_start:
{
uint8_t v___x_5623_; 
v___x_5623_ = lean_usize_dec_eq(v_i_5621_, v_stop_5622_);
if (v___x_5623_ == 0)
{
uint8_t v___x_5624_; lean_object* v___x_5625_; uint8_t v___x_5626_; 
v___x_5624_ = 1;
v___x_5625_ = lean_array_uget_borrowed(v_as_5620_, v_i_5621_);
v___x_5626_ = l_Lean_Expr_isFVar(v___x_5625_);
if (v___x_5626_ == 0)
{
return v___x_5624_;
}
else
{
if (v___x_5623_ == 0)
{
size_t v___x_5627_; size_t v___x_5628_; 
v___x_5627_ = ((size_t)1ULL);
v___x_5628_ = lean_usize_add(v_i_5621_, v___x_5627_);
v_i_5621_ = v___x_5628_;
goto _start;
}
else
{
return v___x_5624_;
}
}
}
else
{
uint8_t v___x_5630_; 
v___x_5630_ = 0;
return v___x_5630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5631_, lean_object* v_i_5632_, lean_object* v_stop_5633_){
_start:
{
size_t v_i_boxed_5634_; size_t v_stop_boxed_5635_; uint8_t v_res_5636_; lean_object* v_r_5637_; 
v_i_boxed_5634_ = lean_unbox_usize(v_i_5632_);
lean_dec(v_i_5632_);
v_stop_boxed_5635_ = lean_unbox_usize(v_stop_5633_);
lean_dec(v_stop_5633_);
v_res_5636_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5631_, v_i_boxed_5634_, v_stop_boxed_5635_);
lean_dec_ref(v_as_5631_);
v_r_5637_ = lean_box(v_res_5636_);
return v_r_5637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5638_, size_t v_sz_5639_, size_t v_i_5640_, lean_object* v_bs_5641_){
_start:
{
uint8_t v___x_5642_; 
v___x_5642_ = lean_usize_dec_lt(v_i_5640_, v_sz_5639_);
if (v___x_5642_ == 0)
{
return v_bs_5641_;
}
else
{
lean_object* v_v_5643_; lean_object* v___x_5644_; lean_object* v_bs_x27_5645_; lean_object* v___y_5647_; 
v_v_5643_ = lean_array_uget(v_bs_5641_, v_i_5640_);
v___x_5644_ = lean_unsigned_to_nat(0u);
v_bs_x27_5645_ = lean_array_uset(v_bs_5641_, v_i_5640_, v___x_5644_);
if (lean_obj_tag(v_v_5643_) == 0)
{
v___y_5647_ = v_v_5643_;
goto v___jp_5646_;
}
else
{
lean_object* v_val_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; 
v_val_5652_ = lean_ctor_get(v_v_5643_, 0);
lean_inc(v_val_5652_);
lean_dec_ref(v_v_5643_);
v___x_5653_ = lean_box(0);
v___x_5654_ = lean_array_get_borrowed(v___x_5653_, v___x_5638_, v_val_5652_);
lean_dec(v_val_5652_);
lean_inc(v___x_5654_);
v___y_5647_ = v___x_5654_;
goto v___jp_5646_;
}
v___jp_5646_:
{
size_t v___x_5648_; size_t v___x_5649_; lean_object* v___x_5650_; 
v___x_5648_ = ((size_t)1ULL);
v___x_5649_ = lean_usize_add(v_i_5640_, v___x_5648_);
v___x_5650_ = lean_array_uset(v_bs_x27_5645_, v_i_5640_, v___y_5647_);
v_i_5640_ = v___x_5649_;
v_bs_5641_ = v___x_5650_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5655_, lean_object* v_sz_5656_, lean_object* v_i_5657_, lean_object* v_bs_5658_){
_start:
{
size_t v_sz_boxed_5659_; size_t v_i_boxed_5660_; lean_object* v_res_5661_; 
v_sz_boxed_5659_ = lean_unbox_usize(v_sz_5656_);
lean_dec(v_sz_5656_);
v_i_boxed_5660_ = lean_unbox_usize(v_i_5657_);
lean_dec(v_i_5657_);
v_res_5661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5655_, v_sz_boxed_5659_, v_i_boxed_5660_, v_bs_5658_);
lean_dec_ref(v___x_5655_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5662_, size_t v_sz_5663_, size_t v_i_5664_, lean_object* v_bs_5665_){
_start:
{
uint8_t v___x_5666_; 
v___x_5666_ = lean_usize_dec_lt(v_i_5664_, v_sz_5663_);
if (v___x_5666_ == 0)
{
return v_bs_5665_;
}
else
{
lean_object* v_v_5667_; lean_object* v___x_5668_; lean_object* v_bs_x27_5669_; size_t v_sz_5670_; size_t v___x_5671_; lean_object* v___x_5672_; size_t v___x_5673_; size_t v___x_5674_; lean_object* v___x_5675_; 
v_v_5667_ = lean_array_uget(v_bs_5665_, v_i_5664_);
v___x_5668_ = lean_unsigned_to_nat(0u);
v_bs_x27_5669_ = lean_array_uset(v_bs_5665_, v_i_5664_, v___x_5668_);
v_sz_5670_ = lean_array_size(v_v_5667_);
v___x_5671_ = ((size_t)0ULL);
v___x_5672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5662_, v_sz_5670_, v___x_5671_, v_v_5667_);
v___x_5673_ = ((size_t)1ULL);
v___x_5674_ = lean_usize_add(v_i_5664_, v___x_5673_);
v___x_5675_ = lean_array_uset(v_bs_x27_5669_, v_i_5664_, v___x_5672_);
v_i_5664_ = v___x_5674_;
v_bs_5665_ = v___x_5675_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5677_, lean_object* v_sz_5678_, lean_object* v_i_5679_, lean_object* v_bs_5680_){
_start:
{
size_t v_sz_boxed_5681_; size_t v_i_boxed_5682_; lean_object* v_res_5683_; 
v_sz_boxed_5681_ = lean_unbox_usize(v_sz_5678_);
lean_dec(v_sz_5678_);
v_i_boxed_5682_ = lean_unbox_usize(v_i_5679_);
lean_dec(v_i_5679_);
v_res_5683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5677_, v_sz_boxed_5681_, v_i_boxed_5682_, v_bs_5680_);
lean_dec_ref(v___x_5677_);
return v_res_5683_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; 
v___x_5686_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5687_ = lean_unsigned_to_nat(6u);
v___x_5688_ = lean_unsigned_to_nat(463u);
v___x_5689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5690_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5691_ = l_mkPanicMessageWithDecl(v___x_5690_, v___x_5689_, v___x_5688_, v___x_5687_, v___x_5686_);
return v___x_5691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5692_, lean_object* v_as_5693_, size_t v_sz_5694_, size_t v_i_5695_, lean_object* v_b_5696_){
_start:
{
lean_object* v_a_5698_; uint8_t v___x_5702_; 
v___x_5702_ = lean_usize_dec_lt(v_i_5695_, v_sz_5694_);
if (v___x_5702_ == 0)
{
return v_b_5696_;
}
else
{
lean_object* v_a_5703_; lean_object* v___x_5704_; uint8_t v_changed_5705_; 
v_a_5703_ = lean_array_uget_borrowed(v_as_5693_, v_i_5695_);
v___x_5704_ = lean_array_get_size(v___x_5692_);
v_changed_5705_ = lean_nat_dec_lt(v_a_5703_, v___x_5704_);
if (v_changed_5705_ == 0)
{
lean_object* v___x_5706_; lean_object* v___x_5707_; 
lean_dec_ref(v_b_5696_);
v___x_5706_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5707_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5706_);
if (lean_obj_tag(v___x_5707_) == 0)
{
lean_object* v_a_5708_; 
v_a_5708_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_a_5708_);
lean_dec_ref(v___x_5707_);
return v_a_5708_;
}
else
{
lean_object* v_a_5709_; 
v_a_5709_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_a_5709_);
lean_dec_ref(v___x_5707_);
v_a_5698_ = v_a_5709_;
goto v___jp_5697_;
}
}
else
{
lean_object* v___x_5710_; lean_object* v___x_5711_; 
v___x_5710_ = lean_box(0);
v___x_5711_ = lean_array_get_borrowed(v___x_5710_, v___x_5692_, v_a_5703_);
if (lean_obj_tag(v___x_5711_) == 1)
{
lean_object* v_val_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; 
v_val_5712_ = lean_ctor_get(v___x_5711_, 0);
v___x_5713_ = lean_box(v_changed_5705_);
v___x_5714_ = lean_array_set(v_b_5696_, v_val_5712_, v___x_5713_);
v_a_5698_ = v___x_5714_;
goto v___jp_5697_;
}
else
{
v_a_5698_ = v_b_5696_;
goto v___jp_5697_;
}
}
}
v___jp_5697_:
{
size_t v___x_5699_; size_t v___x_5700_; 
v___x_5699_ = ((size_t)1ULL);
v___x_5700_ = lean_usize_add(v_i_5695_, v___x_5699_);
v_i_5695_ = v___x_5700_;
v_b_5696_ = v_a_5698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5715_, lean_object* v_as_5716_, lean_object* v_sz_5717_, lean_object* v_i_5718_, lean_object* v_b_5719_){
_start:
{
size_t v_sz_boxed_5720_; size_t v_i_boxed_5721_; lean_object* v_res_5722_; 
v_sz_boxed_5720_ = lean_unbox_usize(v_sz_5717_);
lean_dec(v_sz_5717_);
v_i_boxed_5721_ = lean_unbox_usize(v_i_5718_);
lean_dec(v_i_5718_);
v_res_5722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5715_, v_as_5716_, v_sz_boxed_5720_, v_i_boxed_5721_, v_b_5719_);
lean_dec_ref(v_as_5716_);
lean_dec_ref(v___x_5715_);
return v_res_5722_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5723_, lean_object* v_a_5724_, lean_object* v_b_5725_){
_start:
{
uint8_t v___x_5726_; 
v___x_5726_ = lean_nat_dec_lt(v_a_5724_, v_upperBound_5723_);
if (v___x_5726_ == 0)
{
lean_dec(v_a_5724_);
return v_b_5725_;
}
else
{
lean_object* v_snd_5727_; lean_object* v_snd_5728_; lean_object* v_fst_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5795_; 
v_snd_5727_ = lean_ctor_get(v_b_5725_, 1);
lean_inc(v_snd_5727_);
v_snd_5728_ = lean_ctor_get(v_snd_5727_, 1);
lean_inc(v_snd_5728_);
v_fst_5729_ = lean_ctor_get(v_b_5725_, 0);
v_isSharedCheck_5795_ = !lean_is_exclusive(v_b_5725_);
if (v_isSharedCheck_5795_ == 0)
{
lean_object* v_unused_5796_; 
v_unused_5796_ = lean_ctor_get(v_b_5725_, 1);
lean_dec(v_unused_5796_);
v___x_5731_ = v_b_5725_;
v_isShared_5732_ = v_isSharedCheck_5795_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_fst_5729_);
lean_dec(v_b_5725_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5795_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v_fst_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5793_; 
v_fst_5733_ = lean_ctor_get(v_snd_5727_, 0);
v_isSharedCheck_5793_ = !lean_is_exclusive(v_snd_5727_);
if (v_isSharedCheck_5793_ == 0)
{
lean_object* v_unused_5794_; 
v_unused_5794_ = lean_ctor_get(v_snd_5727_, 1);
lean_dec(v_unused_5794_);
v___x_5735_ = v_snd_5727_;
v_isShared_5736_ = v_isSharedCheck_5793_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_fst_5733_);
lean_dec(v_snd_5727_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5793_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v_array_5737_; lean_object* v_start_5738_; lean_object* v_stop_5739_; uint8_t v___x_5740_; 
v_array_5737_ = lean_ctor_get(v_snd_5728_, 0);
v_start_5738_ = lean_ctor_get(v_snd_5728_, 1);
v_stop_5739_ = lean_ctor_get(v_snd_5728_, 2);
v___x_5740_ = lean_nat_dec_lt(v_start_5738_, v_stop_5739_);
if (v___x_5740_ == 0)
{
lean_object* v___x_5742_; 
lean_dec(v_a_5724_);
if (v_isShared_5736_ == 0)
{
v___x_5742_ = v___x_5735_;
goto v_reusejp_5741_;
}
else
{
lean_object* v_reuseFailAlloc_5746_; 
v_reuseFailAlloc_5746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5746_, 0, v_fst_5733_);
lean_ctor_set(v_reuseFailAlloc_5746_, 1, v_snd_5728_);
v___x_5742_ = v_reuseFailAlloc_5746_;
goto v_reusejp_5741_;
}
v_reusejp_5741_:
{
lean_object* v___x_5744_; 
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 1, v___x_5742_);
v___x_5744_ = v___x_5731_;
goto v_reusejp_5743_;
}
else
{
lean_object* v_reuseFailAlloc_5745_; 
v_reuseFailAlloc_5745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5745_, 0, v_fst_5729_);
lean_ctor_set(v_reuseFailAlloc_5745_, 1, v___x_5742_);
v___x_5744_ = v_reuseFailAlloc_5745_;
goto v_reusejp_5743_;
}
v_reusejp_5743_:
{
return v___x_5744_;
}
}
}
else
{
lean_object* v___x_5748_; uint8_t v_isShared_5749_; uint8_t v_isSharedCheck_5789_; 
lean_inc(v_stop_5739_);
lean_inc(v_start_5738_);
lean_inc_ref(v_array_5737_);
v_isSharedCheck_5789_ = !lean_is_exclusive(v_snd_5728_);
if (v_isSharedCheck_5789_ == 0)
{
lean_object* v_unused_5790_; lean_object* v_unused_5791_; lean_object* v_unused_5792_; 
v_unused_5790_ = lean_ctor_get(v_snd_5728_, 2);
lean_dec(v_unused_5790_);
v_unused_5791_ = lean_ctor_get(v_snd_5728_, 1);
lean_dec(v_unused_5791_);
v_unused_5792_ = lean_ctor_get(v_snd_5728_, 0);
lean_dec(v_unused_5792_);
v___x_5748_ = v_snd_5728_;
v_isShared_5749_ = v_isSharedCheck_5789_;
goto v_resetjp_5747_;
}
else
{
lean_dec(v_snd_5728_);
v___x_5748_ = lean_box(0);
v_isShared_5749_ = v_isSharedCheck_5789_;
goto v_resetjp_5747_;
}
v_resetjp_5747_:
{
lean_object* v_array_5750_; lean_object* v_start_5751_; lean_object* v_stop_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5757_; 
v_array_5750_ = lean_ctor_get(v_fst_5733_, 0);
v_start_5751_ = lean_ctor_get(v_fst_5733_, 1);
v_stop_5752_ = lean_ctor_get(v_fst_5733_, 2);
v___x_5753_ = lean_array_fget(v_array_5737_, v_start_5738_);
v___x_5754_ = lean_unsigned_to_nat(1u);
v___x_5755_ = lean_nat_add(v_start_5738_, v___x_5754_);
lean_dec(v_start_5738_);
if (v_isShared_5749_ == 0)
{
lean_ctor_set(v___x_5748_, 1, v___x_5755_);
v___x_5757_ = v___x_5748_;
goto v_reusejp_5756_;
}
else
{
lean_object* v_reuseFailAlloc_5788_; 
v_reuseFailAlloc_5788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5788_, 0, v_array_5737_);
lean_ctor_set(v_reuseFailAlloc_5788_, 1, v___x_5755_);
lean_ctor_set(v_reuseFailAlloc_5788_, 2, v_stop_5739_);
v___x_5757_ = v_reuseFailAlloc_5788_;
goto v_reusejp_5756_;
}
v_reusejp_5756_:
{
uint8_t v___x_5758_; 
v___x_5758_ = lean_nat_dec_lt(v_start_5751_, v_stop_5752_);
if (v___x_5758_ == 0)
{
lean_object* v___x_5760_; 
lean_dec(v___x_5753_);
lean_dec(v_a_5724_);
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 1, v___x_5757_);
v___x_5760_ = v___x_5735_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5764_; 
v_reuseFailAlloc_5764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5764_, 0, v_fst_5733_);
lean_ctor_set(v_reuseFailAlloc_5764_, 1, v___x_5757_);
v___x_5760_ = v_reuseFailAlloc_5764_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
lean_object* v___x_5762_; 
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 1, v___x_5760_);
v___x_5762_ = v___x_5731_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_fst_5729_);
lean_ctor_set(v_reuseFailAlloc_5763_, 1, v___x_5760_);
v___x_5762_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
return v___x_5762_;
}
}
}
else
{
lean_object* v___x_5766_; uint8_t v_isShared_5767_; uint8_t v_isSharedCheck_5784_; 
lean_inc(v_stop_5752_);
lean_inc(v_start_5751_);
lean_inc_ref(v_array_5750_);
v_isSharedCheck_5784_ = !lean_is_exclusive(v_fst_5733_);
if (v_isSharedCheck_5784_ == 0)
{
lean_object* v_unused_5785_; lean_object* v_unused_5786_; lean_object* v_unused_5787_; 
v_unused_5785_ = lean_ctor_get(v_fst_5733_, 2);
lean_dec(v_unused_5785_);
v_unused_5786_ = lean_ctor_get(v_fst_5733_, 1);
lean_dec(v_unused_5786_);
v_unused_5787_ = lean_ctor_get(v_fst_5733_, 0);
lean_dec(v_unused_5787_);
v___x_5766_ = v_fst_5733_;
v_isShared_5767_ = v_isSharedCheck_5784_;
goto v_resetjp_5765_;
}
else
{
lean_dec(v_fst_5733_);
v___x_5766_ = lean_box(0);
v_isShared_5767_ = v_isSharedCheck_5784_;
goto v_resetjp_5765_;
}
v_resetjp_5765_:
{
lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5771_; 
v___x_5768_ = lean_array_fget(v_array_5750_, v_start_5751_);
v___x_5769_ = lean_nat_add(v_start_5751_, v___x_5754_);
lean_dec(v_start_5751_);
if (v_isShared_5767_ == 0)
{
lean_ctor_set(v___x_5766_, 1, v___x_5769_);
v___x_5771_ = v___x_5766_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_array_5750_);
lean_ctor_set(v_reuseFailAlloc_5783_, 1, v___x_5769_);
lean_ctor_set(v_reuseFailAlloc_5783_, 2, v_stop_5752_);
v___x_5771_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
size_t v_sz_5772_; size_t v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5776_; 
v_sz_5772_ = lean_array_size(v___x_5768_);
v___x_5773_ = ((size_t)0ULL);
v___x_5774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5753_, v___x_5768_, v_sz_5772_, v___x_5773_, v_fst_5729_);
lean_dec(v___x_5768_);
lean_dec(v___x_5753_);
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 1, v___x_5757_);
lean_ctor_set(v___x_5735_, 0, v___x_5771_);
v___x_5776_ = v___x_5735_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5782_; 
v_reuseFailAlloc_5782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5782_, 0, v___x_5771_);
lean_ctor_set(v_reuseFailAlloc_5782_, 1, v___x_5757_);
v___x_5776_ = v_reuseFailAlloc_5782_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
lean_object* v___x_5778_; 
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 1, v___x_5776_);
lean_ctor_set(v___x_5731_, 0, v___x_5774_);
v___x_5778_ = v___x_5731_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v___x_5774_);
lean_ctor_set(v_reuseFailAlloc_5781_, 1, v___x_5776_);
v___x_5778_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
lean_object* v___x_5779_; 
v___x_5779_ = lean_nat_add(v_a_5724_, v___x_5754_);
lean_dec(v_a_5724_);
v_a_5724_ = v___x_5779_;
v_b_5725_ = v___x_5778_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_5797_, lean_object* v_a_5798_, lean_object* v_b_5799_){
_start:
{
lean_object* v_res_5800_; 
v_res_5800_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_5797_, v_a_5798_, v_b_5799_);
lean_dec(v_upperBound_5797_);
return v_res_5800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5801_, uint8_t v___x_5802_, lean_object* v_as_5803_, size_t v_sz_5804_, size_t v_i_5805_, lean_object* v_b_5806_){
_start:
{
lean_object* v_a_5808_; uint8_t v___x_5812_; 
v___x_5812_ = lean_usize_dec_lt(v_i_5805_, v_sz_5804_);
if (v___x_5812_ == 0)
{
return v_b_5806_;
}
else
{
lean_object* v_fst_5813_; lean_object* v_snd_5814_; lean_object* v___x_5816_; uint8_t v_isShared_5817_; uint8_t v_isSharedCheck_5835_; 
v_fst_5813_ = lean_ctor_get(v_b_5806_, 0);
v_snd_5814_ = lean_ctor_get(v_b_5806_, 1);
v_isSharedCheck_5835_ = !lean_is_exclusive(v_b_5806_);
if (v_isSharedCheck_5835_ == 0)
{
v___x_5816_ = v_b_5806_;
v_isShared_5817_ = v_isSharedCheck_5835_;
goto v_resetjp_5815_;
}
else
{
lean_inc(v_snd_5814_);
lean_inc(v_fst_5813_);
lean_dec(v_b_5806_);
v___x_5816_ = lean_box(0);
v_isShared_5817_ = v_isSharedCheck_5835_;
goto v_resetjp_5815_;
}
v_resetjp_5815_:
{
lean_object* v_a_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; 
v_a_5822_ = lean_array_uget_borrowed(v_as_5803_, v_i_5805_);
v___x_5823_ = lean_box(0);
v___x_5824_ = lean_array_get_borrowed(v___x_5823_, v___x_5801_, v_a_5822_);
if (lean_obj_tag(v___x_5824_) == 1)
{
lean_object* v_val_5825_; uint8_t v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; uint8_t v___x_5829_; 
v_val_5825_ = lean_ctor_get(v___x_5824_, 0);
v___x_5826_ = 0;
v___x_5827_ = lean_box(v___x_5826_);
v___x_5828_ = lean_array_get_borrowed(v___x_5827_, v_fst_5813_, v_val_5825_);
v___x_5829_ = lean_unbox(v___x_5828_);
if (v___x_5829_ == 0)
{
if (v___x_5802_ == 0)
{
goto v___jp_5818_;
}
else
{
lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; 
lean_del_object(v___x_5816_);
lean_dec(v_snd_5814_);
v___x_5830_ = lean_box(v___x_5802_);
v___x_5831_ = lean_array_set(v_fst_5813_, v_val_5825_, v___x_5830_);
v___x_5832_ = lean_box(v___x_5802_);
v___x_5833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5833_, 0, v___x_5831_);
lean_ctor_set(v___x_5833_, 1, v___x_5832_);
v_a_5808_ = v___x_5833_;
goto v___jp_5807_;
}
}
else
{
goto v___jp_5818_;
}
}
else
{
lean_object* v___x_5834_; 
lean_del_object(v___x_5816_);
v___x_5834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5834_, 0, v_fst_5813_);
lean_ctor_set(v___x_5834_, 1, v_snd_5814_);
v_a_5808_ = v___x_5834_;
goto v___jp_5807_;
}
v___jp_5818_:
{
lean_object* v___x_5820_; 
if (v_isShared_5817_ == 0)
{
v___x_5820_ = v___x_5816_;
goto v_reusejp_5819_;
}
else
{
lean_object* v_reuseFailAlloc_5821_; 
v_reuseFailAlloc_5821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5821_, 0, v_fst_5813_);
lean_ctor_set(v_reuseFailAlloc_5821_, 1, v_snd_5814_);
v___x_5820_ = v_reuseFailAlloc_5821_;
goto v_reusejp_5819_;
}
v_reusejp_5819_:
{
v_a_5808_ = v___x_5820_;
goto v___jp_5807_;
}
}
}
}
v___jp_5807_:
{
size_t v___x_5809_; size_t v___x_5810_; 
v___x_5809_ = ((size_t)1ULL);
v___x_5810_ = lean_usize_add(v_i_5805_, v___x_5809_);
v_i_5805_ = v___x_5810_;
v_b_5806_ = v_a_5808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5836_, lean_object* v___x_5837_, lean_object* v_as_5838_, lean_object* v_sz_5839_, lean_object* v_i_5840_, lean_object* v_b_5841_){
_start:
{
uint8_t v___x_8471__boxed_5842_; size_t v_sz_boxed_5843_; size_t v_i_boxed_5844_; lean_object* v_res_5845_; 
v___x_8471__boxed_5842_ = lean_unbox(v___x_5837_);
v_sz_boxed_5843_ = lean_unbox_usize(v_sz_5839_);
lean_dec(v_sz_5839_);
v_i_boxed_5844_ = lean_unbox_usize(v_i_5840_);
lean_dec(v_i_5840_);
v_res_5845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5836_, v___x_8471__boxed_5842_, v_as_5838_, v_sz_boxed_5843_, v_i_boxed_5844_, v_b_5841_);
lean_dec_ref(v_as_5838_);
lean_dec_ref(v___x_5836_);
return v_res_5845_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5846_, lean_object* v___x_5847_, lean_object* v_fixedParamPerms_5848_, lean_object* v_next_5849_, lean_object* v_a_5850_, lean_object* v_b_5851_){
_start:
{
lean_object* v_a_5853_; uint8_t v___x_5857_; 
v___x_5857_ = lean_nat_dec_lt(v_a_5850_, v_upperBound_5846_);
if (v___x_5857_ == 0)
{
lean_dec(v_a_5850_);
return v_b_5851_;
}
else
{
lean_object* v_fst_5858_; lean_object* v_snd_5859_; lean_object* v___x_5861_; uint8_t v_isShared_5862_; uint8_t v_isSharedCheck_5895_; 
v_fst_5858_ = lean_ctor_get(v_b_5851_, 0);
v_snd_5859_ = lean_ctor_get(v_b_5851_, 1);
v_isSharedCheck_5895_ = !lean_is_exclusive(v_b_5851_);
if (v_isSharedCheck_5895_ == 0)
{
v___x_5861_ = v_b_5851_;
v_isShared_5862_ = v_isSharedCheck_5895_;
goto v_resetjp_5860_;
}
else
{
lean_inc(v_snd_5859_);
lean_inc(v_fst_5858_);
lean_dec(v_b_5851_);
v___x_5861_ = lean_box(0);
v_isShared_5862_ = v_isSharedCheck_5895_;
goto v_resetjp_5860_;
}
v_resetjp_5860_:
{
lean_object* v___x_5863_; 
v___x_5863_ = lean_array_fget_borrowed(v___x_5847_, v_a_5850_);
if (lean_obj_tag(v___x_5863_) == 1)
{
lean_object* v_val_5864_; uint8_t v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; uint8_t v___x_5868_; 
v_val_5864_ = lean_ctor_get(v___x_5863_, 0);
v___x_5865_ = 0;
v___x_5866_ = lean_box(v___x_5865_);
v___x_5867_ = lean_array_get_borrowed(v___x_5866_, v_fst_5858_, v_val_5864_);
v___x_5868_ = lean_unbox(v___x_5867_);
if (v___x_5868_ == 0)
{
lean_object* v___x_5870_; 
if (v_isShared_5862_ == 0)
{
v___x_5870_ = v___x_5861_;
goto v_reusejp_5869_;
}
else
{
lean_object* v_reuseFailAlloc_5871_; 
v_reuseFailAlloc_5871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5871_, 0, v_fst_5858_);
lean_ctor_set(v_reuseFailAlloc_5871_, 1, v_snd_5859_);
v___x_5870_ = v_reuseFailAlloc_5871_;
goto v_reusejp_5869_;
}
v_reusejp_5869_:
{
v_a_5853_ = v___x_5870_;
goto v___jp_5852_;
}
}
else
{
lean_object* v_revDeps_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5877_; 
lean_inc(v___x_5867_);
v_revDeps_5872_ = lean_ctor_get(v_fixedParamPerms_5848_, 2);
v___x_5873_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_5874_ = lean_array_get_borrowed(v___x_5873_, v_revDeps_5872_, v_next_5849_);
v___x_5875_ = lean_array_get_borrowed(v___x_5873_, v___x_5874_, v_a_5850_);
if (v_isShared_5862_ == 0)
{
v___x_5877_ = v___x_5861_;
goto v_reusejp_5876_;
}
else
{
lean_object* v_reuseFailAlloc_5891_; 
v_reuseFailAlloc_5891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5891_, 0, v_fst_5858_);
lean_ctor_set(v_reuseFailAlloc_5891_, 1, v_snd_5859_);
v___x_5877_ = v_reuseFailAlloc_5891_;
goto v_reusejp_5876_;
}
v_reusejp_5876_:
{
size_t v_sz_5878_; size_t v___x_5879_; uint8_t v___x_5880_; lean_object* v___x_5881_; lean_object* v_fst_5882_; lean_object* v_snd_5883_; lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5890_; 
v_sz_5878_ = lean_array_size(v___x_5875_);
v___x_5879_ = ((size_t)0ULL);
v___x_5880_ = lean_unbox(v___x_5867_);
lean_dec(v___x_5867_);
v___x_5881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5847_, v___x_5880_, v___x_5875_, v_sz_5878_, v___x_5879_, v___x_5877_);
v_fst_5882_ = lean_ctor_get(v___x_5881_, 0);
v_snd_5883_ = lean_ctor_get(v___x_5881_, 1);
v_isSharedCheck_5890_ = !lean_is_exclusive(v___x_5881_);
if (v_isSharedCheck_5890_ == 0)
{
v___x_5885_ = v___x_5881_;
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
else
{
lean_inc(v_snd_5883_);
lean_inc(v_fst_5882_);
lean_dec(v___x_5881_);
v___x_5885_ = lean_box(0);
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
v_resetjp_5884_:
{
lean_object* v___x_5888_; 
if (v_isShared_5886_ == 0)
{
v___x_5888_ = v___x_5885_;
goto v_reusejp_5887_;
}
else
{
lean_object* v_reuseFailAlloc_5889_; 
v_reuseFailAlloc_5889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5889_, 0, v_fst_5882_);
lean_ctor_set(v_reuseFailAlloc_5889_, 1, v_snd_5883_);
v___x_5888_ = v_reuseFailAlloc_5889_;
goto v_reusejp_5887_;
}
v_reusejp_5887_:
{
v_a_5853_ = v___x_5888_;
goto v___jp_5852_;
}
}
}
}
}
else
{
lean_object* v___x_5893_; 
if (v_isShared_5862_ == 0)
{
v___x_5893_ = v___x_5861_;
goto v_reusejp_5892_;
}
else
{
lean_object* v_reuseFailAlloc_5894_; 
v_reuseFailAlloc_5894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5894_, 0, v_fst_5858_);
lean_ctor_set(v_reuseFailAlloc_5894_, 1, v_snd_5859_);
v___x_5893_ = v_reuseFailAlloc_5894_;
goto v_reusejp_5892_;
}
v_reusejp_5892_:
{
v_a_5853_ = v___x_5893_;
goto v___jp_5852_;
}
}
}
}
v___jp_5852_:
{
lean_object* v___x_5854_; lean_object* v___x_5855_; 
v___x_5854_ = lean_unsigned_to_nat(1u);
v___x_5855_ = lean_nat_add(v_a_5850_, v___x_5854_);
lean_dec(v_a_5850_);
v_a_5850_ = v___x_5855_;
v_b_5851_ = v_a_5853_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5896_, lean_object* v___x_5897_, lean_object* v_fixedParamPerms_5898_, lean_object* v_next_5899_, lean_object* v_a_5900_, lean_object* v_b_5901_){
_start:
{
lean_object* v_res_5902_; 
v_res_5902_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5896_, v___x_5897_, v_fixedParamPerms_5898_, v_next_5899_, v_a_5900_, v_b_5901_);
lean_dec(v_next_5899_);
lean_dec_ref(v_fixedParamPerms_5898_);
lean_dec_ref(v___x_5897_);
lean_dec(v_upperBound_5896_);
return v_res_5902_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5903_, lean_object* v___x_5904_, lean_object* v_fixedParamPerms_5905_, lean_object* v_a_5906_, lean_object* v_b_5907_){
_start:
{
uint8_t v___x_5908_; 
v___x_5908_ = lean_nat_dec_lt(v_a_5906_, v_upperBound_5903_);
if (v___x_5908_ == 0)
{
lean_dec(v_a_5906_);
return v_b_5907_;
}
else
{
lean_object* v_fst_5909_; lean_object* v_snd_5910_; lean_object* v___x_5912_; uint8_t v_isShared_5913_; uint8_t v_isSharedCheck_5933_; 
v_fst_5909_ = lean_ctor_get(v_b_5907_, 0);
v_snd_5910_ = lean_ctor_get(v_b_5907_, 1);
v_isSharedCheck_5933_ = !lean_is_exclusive(v_b_5907_);
if (v_isSharedCheck_5933_ == 0)
{
v___x_5912_ = v_b_5907_;
v_isShared_5913_ = v_isSharedCheck_5933_;
goto v_resetjp_5911_;
}
else
{
lean_inc(v_snd_5910_);
lean_inc(v_fst_5909_);
lean_dec(v_b_5907_);
v___x_5912_ = lean_box(0);
v_isShared_5913_ = v_isSharedCheck_5933_;
goto v_resetjp_5911_;
}
v_resetjp_5911_:
{
lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5918_; 
v___x_5914_ = lean_array_fget_borrowed(v___x_5904_, v_a_5906_);
v___x_5915_ = lean_array_get_size(v___x_5914_);
v___x_5916_ = lean_unsigned_to_nat(0u);
if (v_isShared_5913_ == 0)
{
v___x_5918_ = v___x_5912_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5932_; 
v_reuseFailAlloc_5932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5932_, 0, v_fst_5909_);
lean_ctor_set(v_reuseFailAlloc_5932_, 1, v_snd_5910_);
v___x_5918_ = v_reuseFailAlloc_5932_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
lean_object* v___x_5919_; lean_object* v_fst_5920_; lean_object* v_snd_5921_; lean_object* v___x_5923_; uint8_t v_isShared_5924_; uint8_t v_isSharedCheck_5931_; 
v___x_5919_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5915_, v___x_5914_, v_fixedParamPerms_5905_, v_a_5906_, v___x_5916_, v___x_5918_);
v_fst_5920_ = lean_ctor_get(v___x_5919_, 0);
v_snd_5921_ = lean_ctor_get(v___x_5919_, 1);
v_isSharedCheck_5931_ = !lean_is_exclusive(v___x_5919_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5923_ = v___x_5919_;
v_isShared_5924_ = v_isSharedCheck_5931_;
goto v_resetjp_5922_;
}
else
{
lean_inc(v_snd_5921_);
lean_inc(v_fst_5920_);
lean_dec(v___x_5919_);
v___x_5923_ = lean_box(0);
v_isShared_5924_ = v_isSharedCheck_5931_;
goto v_resetjp_5922_;
}
v_resetjp_5922_:
{
lean_object* v___x_5926_; 
if (v_isShared_5924_ == 0)
{
v___x_5926_ = v___x_5923_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_5930_; 
v_reuseFailAlloc_5930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5930_, 0, v_fst_5920_);
lean_ctor_set(v_reuseFailAlloc_5930_, 1, v_snd_5921_);
v___x_5926_ = v_reuseFailAlloc_5930_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; 
v___x_5927_ = lean_unsigned_to_nat(1u);
v___x_5928_ = lean_nat_add(v_a_5906_, v___x_5927_);
lean_dec(v_a_5906_);
v_a_5906_ = v___x_5928_;
v_b_5907_ = v___x_5926_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5934_, lean_object* v___x_5935_, lean_object* v_fixedParamPerms_5936_, lean_object* v_a_5937_, lean_object* v_b_5938_){
_start:
{
lean_object* v_res_5939_; 
v_res_5939_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5934_, v___x_5935_, v_fixedParamPerms_5936_, v_a_5937_, v_b_5938_);
lean_dec_ref(v_fixedParamPerms_5936_);
lean_dec_ref(v___x_5935_);
lean_dec(v_upperBound_5934_);
return v_res_5939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_5940_, lean_object* v___x_5941_, lean_object* v_fixedParamPerms_5942_, lean_object* v_b_5943_){
_start:
{
lean_object* v_snd_5944_; uint8_t v___x_5945_; 
v_snd_5944_ = lean_ctor_get(v_b_5943_, 1);
v___x_5945_ = lean_unbox(v_snd_5944_);
if (v___x_5945_ == 0)
{
lean_object* v_fst_5946_; lean_object* v___x_5948_; uint8_t v_isShared_5949_; uint8_t v_isSharedCheck_5953_; 
lean_inc(v_snd_5944_);
v_fst_5946_ = lean_ctor_get(v_b_5943_, 0);
v_isSharedCheck_5953_ = !lean_is_exclusive(v_b_5943_);
if (v_isSharedCheck_5953_ == 0)
{
lean_object* v_unused_5954_; 
v_unused_5954_ = lean_ctor_get(v_b_5943_, 1);
lean_dec(v_unused_5954_);
v___x_5948_ = v_b_5943_;
v_isShared_5949_ = v_isSharedCheck_5953_;
goto v_resetjp_5947_;
}
else
{
lean_inc(v_fst_5946_);
lean_dec(v_b_5943_);
v___x_5948_ = lean_box(0);
v_isShared_5949_ = v_isSharedCheck_5953_;
goto v_resetjp_5947_;
}
v_resetjp_5947_:
{
lean_object* v___x_5951_; 
if (v_isShared_5949_ == 0)
{
v___x_5951_ = v___x_5948_;
goto v_reusejp_5950_;
}
else
{
lean_object* v_reuseFailAlloc_5952_; 
v_reuseFailAlloc_5952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_fst_5946_);
lean_ctor_set(v_reuseFailAlloc_5952_, 1, v_snd_5944_);
v___x_5951_ = v_reuseFailAlloc_5952_;
goto v_reusejp_5950_;
}
v_reusejp_5950_:
{
return v___x_5951_;
}
}
}
else
{
lean_object* v_fst_5955_; lean_object* v___x_5957_; uint8_t v_isShared_5958_; uint8_t v_isSharedCheck_5976_; 
v_fst_5955_ = lean_ctor_get(v_b_5943_, 0);
v_isSharedCheck_5976_ = !lean_is_exclusive(v_b_5943_);
if (v_isSharedCheck_5976_ == 0)
{
lean_object* v_unused_5977_; 
v_unused_5977_ = lean_ctor_get(v_b_5943_, 1);
lean_dec(v_unused_5977_);
v___x_5957_ = v_b_5943_;
v_isShared_5958_ = v_isSharedCheck_5976_;
goto v_resetjp_5956_;
}
else
{
lean_inc(v_fst_5955_);
lean_dec(v_b_5943_);
v___x_5957_ = lean_box(0);
v_isShared_5958_ = v_isSharedCheck_5976_;
goto v_resetjp_5956_;
}
v_resetjp_5956_:
{
uint8_t v_changed_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5963_; 
v_changed_5959_ = 0;
v___x_5960_ = lean_unsigned_to_nat(0u);
v___x_5961_ = lean_box(v_changed_5959_);
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 1, v___x_5961_);
v___x_5963_ = v___x_5957_;
goto v_reusejp_5962_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v_fst_5955_);
lean_ctor_set(v_reuseFailAlloc_5975_, 1, v___x_5961_);
v___x_5963_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5962_;
}
v_reusejp_5962_:
{
lean_object* v___x_5964_; lean_object* v_fst_5965_; lean_object* v_snd_5966_; lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_5974_; 
v___x_5964_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5940_, v___x_5941_, v_fixedParamPerms_5942_, v___x_5960_, v___x_5963_);
v_fst_5965_ = lean_ctor_get(v___x_5964_, 0);
v_snd_5966_ = lean_ctor_get(v___x_5964_, 1);
v_isSharedCheck_5974_ = !lean_is_exclusive(v___x_5964_);
if (v_isSharedCheck_5974_ == 0)
{
v___x_5968_ = v___x_5964_;
v_isShared_5969_ = v_isSharedCheck_5974_;
goto v_resetjp_5967_;
}
else
{
lean_inc(v_snd_5966_);
lean_inc(v_fst_5965_);
lean_dec(v___x_5964_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_5974_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
lean_object* v___x_5971_; 
if (v_isShared_5969_ == 0)
{
v___x_5971_ = v___x_5968_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5973_; 
v_reuseFailAlloc_5973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5973_, 0, v_fst_5965_);
lean_ctor_set(v_reuseFailAlloc_5973_, 1, v_snd_5966_);
v___x_5971_ = v_reuseFailAlloc_5973_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
v_b_5943_ = v___x_5971_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_5978_, lean_object* v___x_5979_, lean_object* v_fixedParamPerms_5980_, lean_object* v_b_5981_){
_start:
{
lean_object* v_res_5982_; 
v_res_5982_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_5978_, v___x_5979_, v_fixedParamPerms_5980_, v_b_5981_);
lean_dec_ref(v_fixedParamPerms_5980_);
lean_dec_ref(v___x_5979_);
lean_dec(v___x_5978_);
return v_res_5982_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; 
v___x_5984_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_5985_ = lean_unsigned_to_nat(2u);
v___x_5986_ = lean_unsigned_to_nat(457u);
v___x_5987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5988_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5989_ = l_mkPanicMessageWithDecl(v___x_5988_, v___x_5987_, v___x_5986_, v___x_5985_, v___x_5984_);
return v___x_5989_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; 
v___x_5991_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_5992_ = lean_unsigned_to_nat(2u);
v___x_5993_ = lean_unsigned_to_nat(458u);
v___x_5994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5995_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5996_ = l_mkPanicMessageWithDecl(v___x_5995_, v___x_5994_, v___x_5993_, v___x_5992_, v___x_5991_);
return v___x_5996_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; 
v___x_5998_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_5999_ = lean_unsigned_to_nat(2u);
v___x_6000_ = lean_unsigned_to_nat(456u);
v___x_6001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6002_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6003_ = l_mkPanicMessageWithDecl(v___x_6002_, v___x_6001_, v___x_6000_, v___x_5999_, v___x_5998_);
return v___x_6003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6004_, lean_object* v_xs_6005_, lean_object* v_toErase_6006_){
_start:
{
lean_object* v___x_6007_; lean_object* v___x_6008_; uint8_t v___x_6092_; 
v___x_6007_ = lean_unsigned_to_nat(0u);
v___x_6008_ = lean_array_get_size(v_xs_6005_);
v___x_6092_ = lean_nat_dec_lt(v___x_6007_, v___x_6008_);
if (v___x_6092_ == 0)
{
goto v___jp_6009_;
}
else
{
if (v___x_6092_ == 0)
{
goto v___jp_6009_;
}
else
{
size_t v___x_6093_; size_t v___x_6094_; uint8_t v___x_6095_; 
v___x_6093_ = ((size_t)0ULL);
v___x_6094_ = lean_usize_of_nat(v___x_6008_);
v___x_6095_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6005_, v___x_6093_, v___x_6094_);
if (v___x_6095_ == 0)
{
goto v___jp_6009_;
}
else
{
lean_object* v___x_6096_; lean_object* v___x_6097_; 
lean_dec_ref(v_toErase_6006_);
lean_dec_ref(v_xs_6005_);
lean_dec_ref(v_fixedParamPerms_6004_);
v___x_6096_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6097_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6096_);
return v___x_6097_;
}
}
}
v___jp_6009_:
{
lean_object* v_numFixed_6010_; lean_object* v_perms_6011_; lean_object* v_revDeps_6012_; uint8_t v___x_6013_; 
v_numFixed_6010_ = lean_ctor_get(v_fixedParamPerms_6004_, 0);
v_perms_6011_ = lean_ctor_get(v_fixedParamPerms_6004_, 1);
lean_inc_ref(v_perms_6011_);
v_revDeps_6012_ = lean_ctor_get(v_fixedParamPerms_6004_, 2);
lean_inc_ref(v_revDeps_6012_);
v___x_6013_ = lean_nat_dec_eq(v_numFixed_6010_, v___x_6008_);
if (v___x_6013_ == 0)
{
lean_object* v___x_6014_; lean_object* v___x_6015_; 
lean_dec_ref(v_revDeps_6012_);
lean_dec_ref(v_perms_6011_);
lean_dec_ref(v_toErase_6006_);
lean_dec_ref(v_xs_6005_);
lean_dec_ref(v_fixedParamPerms_6004_);
v___x_6014_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6015_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6014_);
return v___x_6015_;
}
else
{
lean_object* v___x_6016_; lean_object* v___x_6017_; uint8_t v_changed_6018_; 
v___x_6016_ = lean_array_get_size(v_toErase_6006_);
v___x_6017_ = lean_array_get_size(v_perms_6011_);
v_changed_6018_ = lean_nat_dec_eq(v___x_6016_, v___x_6017_);
if (v_changed_6018_ == 0)
{
lean_object* v___x_6019_; lean_object* v___x_6020_; 
lean_dec_ref(v_revDeps_6012_);
lean_dec_ref(v_perms_6011_);
lean_dec_ref(v_toErase_6006_);
lean_dec_ref(v_xs_6005_);
lean_dec_ref(v_fixedParamPerms_6004_);
v___x_6019_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6020_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6019_);
return v___x_6020_;
}
else
{
uint8_t v_changed_6021_; lean_object* v___x_6022_; lean_object* v_mask_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v_fst_6029_; lean_object* v___x_6031_; uint8_t v_isShared_6032_; uint8_t v_isSharedCheck_6090_; 
v_changed_6021_ = 0;
v___x_6022_ = lean_box(v_changed_6021_);
lean_inc(v_numFixed_6010_);
v_mask_6023_ = lean_mk_array(v_numFixed_6010_, v___x_6022_);
v___x_6024_ = l_Array_toSubarray___redArg(v_toErase_6006_, v___x_6007_, v___x_6016_);
lean_inc_ref(v_perms_6011_);
v___x_6025_ = l_Array_toSubarray___redArg(v_perms_6011_, v___x_6007_, v___x_6017_);
v___x_6026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6024_);
lean_ctor_set(v___x_6026_, 1, v___x_6025_);
v___x_6027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6027_, 0, v_mask_6023_);
lean_ctor_set(v___x_6027_, 1, v___x_6026_);
v___x_6028_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6016_, v___x_6007_, v___x_6027_);
v_fst_6029_ = lean_ctor_get(v___x_6028_, 0);
v_isSharedCheck_6090_ = !lean_is_exclusive(v___x_6028_);
if (v_isSharedCheck_6090_ == 0)
{
lean_object* v_unused_6091_; 
v_unused_6091_ = lean_ctor_get(v___x_6028_, 1);
lean_dec(v_unused_6091_);
v___x_6031_ = v___x_6028_;
v_isShared_6032_ = v_isSharedCheck_6090_;
goto v_resetjp_6030_;
}
else
{
lean_inc(v_fst_6029_);
lean_dec(v___x_6028_);
v___x_6031_ = lean_box(0);
v_isShared_6032_ = v_isSharedCheck_6090_;
goto v_resetjp_6030_;
}
v_resetjp_6030_:
{
lean_object* v___x_6033_; lean_object* v___x_6035_; 
v___x_6033_ = lean_box(v_changed_6018_);
if (v_isShared_6032_ == 0)
{
lean_ctor_set(v___x_6031_, 1, v___x_6033_);
v___x_6035_ = v___x_6031_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6089_; 
v_reuseFailAlloc_6089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6089_, 0, v_fst_6029_);
lean_ctor_set(v_reuseFailAlloc_6089_, 1, v___x_6033_);
v___x_6035_ = v_reuseFailAlloc_6089_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
lean_object* v___x_6036_; lean_object* v___x_6038_; uint8_t v_isShared_6039_; uint8_t v_isSharedCheck_6085_; 
v___x_6036_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6017_, v_perms_6011_, v_fixedParamPerms_6004_, v___x_6035_);
v_isSharedCheck_6085_ = !lean_is_exclusive(v_fixedParamPerms_6004_);
if (v_isSharedCheck_6085_ == 0)
{
lean_object* v_unused_6086_; lean_object* v_unused_6087_; lean_object* v_unused_6088_; 
v_unused_6086_ = lean_ctor_get(v_fixedParamPerms_6004_, 2);
lean_dec(v_unused_6086_);
v_unused_6087_ = lean_ctor_get(v_fixedParamPerms_6004_, 1);
lean_dec(v_unused_6087_);
v_unused_6088_ = lean_ctor_get(v_fixedParamPerms_6004_, 0);
lean_dec(v_unused_6088_);
v___x_6038_ = v_fixedParamPerms_6004_;
v_isShared_6039_ = v_isSharedCheck_6085_;
goto v_resetjp_6037_;
}
else
{
lean_dec(v_fixedParamPerms_6004_);
v___x_6038_ = lean_box(0);
v_isShared_6039_ = v_isSharedCheck_6085_;
goto v_resetjp_6037_;
}
v_resetjp_6037_:
{
lean_object* v_fst_6040_; lean_object* v___x_6042_; uint8_t v_isShared_6043_; uint8_t v_isSharedCheck_6083_; 
v_fst_6040_ = lean_ctor_get(v___x_6036_, 0);
v_isSharedCheck_6083_ = !lean_is_exclusive(v___x_6036_);
if (v_isSharedCheck_6083_ == 0)
{
lean_object* v_unused_6084_; 
v_unused_6084_ = lean_ctor_get(v___x_6036_, 1);
lean_dec(v_unused_6084_);
v___x_6042_ = v___x_6036_;
v_isShared_6043_ = v_isSharedCheck_6083_;
goto v_resetjp_6041_;
}
else
{
lean_inc(v_fst_6040_);
lean_dec(v___x_6036_);
v___x_6042_ = lean_box(0);
v_isShared_6043_ = v_isSharedCheck_6083_;
goto v_resetjp_6041_;
}
v_resetjp_6041_:
{
lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6049_; 
v___x_6044_ = lean_array_get_size(v_fst_6040_);
v___x_6045_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6046_ = l_Array_toSubarray___redArg(v_fst_6040_, v___x_6007_, v___x_6044_);
v___x_6047_ = l_Array_toSubarray___redArg(v_xs_6005_, v___x_6007_, v___x_6008_);
if (v_isShared_6043_ == 0)
{
lean_ctor_set(v___x_6042_, 1, v___x_6047_);
lean_ctor_set(v___x_6042_, 0, v___x_6046_);
v___x_6049_ = v___x_6042_;
goto v_reusejp_6048_;
}
else
{
lean_object* v_reuseFailAlloc_6082_; 
v_reuseFailAlloc_6082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6082_, 0, v___x_6046_);
lean_ctor_set(v_reuseFailAlloc_6082_, 1, v___x_6047_);
v___x_6049_ = v_reuseFailAlloc_6082_;
goto v_reusejp_6048_;
}
v_reusejp_6048_:
{
lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v_snd_6054_; lean_object* v_snd_6055_; lean_object* v_fst_6056_; lean_object* v_fst_6057_; lean_object* v___x_6059_; uint8_t v_isShared_6060_; uint8_t v_isSharedCheck_6080_; 
v___x_6050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6045_);
lean_ctor_set(v___x_6050_, 1, v___x_6049_);
v___x_6051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6051_, 0, v___x_6045_);
lean_ctor_set(v___x_6051_, 1, v___x_6050_);
v___x_6052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___x_6045_);
lean_ctor_set(v___x_6052_, 1, v___x_6051_);
v___x_6053_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6044_, v___x_6007_, v___x_6052_);
v_snd_6054_ = lean_ctor_get(v___x_6053_, 1);
lean_inc(v_snd_6054_);
v_snd_6055_ = lean_ctor_get(v_snd_6054_, 1);
lean_inc(v_snd_6055_);
v_fst_6056_ = lean_ctor_get(v___x_6053_, 0);
lean_inc(v_fst_6056_);
lean_dec_ref(v___x_6053_);
v_fst_6057_ = lean_ctor_get(v_snd_6054_, 0);
v_isSharedCheck_6080_ = !lean_is_exclusive(v_snd_6054_);
if (v_isSharedCheck_6080_ == 0)
{
lean_object* v_unused_6081_; 
v_unused_6081_ = lean_ctor_get(v_snd_6054_, 1);
lean_dec(v_unused_6081_);
v___x_6059_ = v_snd_6054_;
v_isShared_6060_ = v_isSharedCheck_6080_;
goto v_resetjp_6058_;
}
else
{
lean_inc(v_fst_6057_);
lean_dec(v_snd_6054_);
v___x_6059_ = lean_box(0);
v_isShared_6060_ = v_isSharedCheck_6080_;
goto v_resetjp_6058_;
}
v_resetjp_6058_:
{
lean_object* v_fst_6061_; lean_object* v___x_6063_; uint8_t v_isShared_6064_; uint8_t v_isSharedCheck_6078_; 
v_fst_6061_ = lean_ctor_get(v_snd_6055_, 0);
v_isSharedCheck_6078_ = !lean_is_exclusive(v_snd_6055_);
if (v_isSharedCheck_6078_ == 0)
{
lean_object* v_unused_6079_; 
v_unused_6079_ = lean_ctor_get(v_snd_6055_, 1);
lean_dec(v_unused_6079_);
v___x_6063_ = v_snd_6055_;
v_isShared_6064_ = v_isSharedCheck_6078_;
goto v_resetjp_6062_;
}
else
{
lean_inc(v_fst_6061_);
lean_dec(v_snd_6055_);
v___x_6063_ = lean_box(0);
v_isShared_6064_ = v_isSharedCheck_6078_;
goto v_resetjp_6062_;
}
v_resetjp_6062_:
{
lean_object* v___x_6065_; size_t v_sz_6066_; size_t v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6070_; 
v___x_6065_ = lean_array_get_size(v_fst_6061_);
v_sz_6066_ = lean_array_size(v_perms_6011_);
v___x_6067_ = ((size_t)0ULL);
v___x_6068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6056_, v_sz_6066_, v___x_6067_, v_perms_6011_);
lean_dec(v_fst_6056_);
if (v_isShared_6039_ == 0)
{
lean_ctor_set(v___x_6038_, 1, v___x_6068_);
lean_ctor_set(v___x_6038_, 0, v___x_6065_);
v___x_6070_ = v___x_6038_;
goto v_reusejp_6069_;
}
else
{
lean_object* v_reuseFailAlloc_6077_; 
v_reuseFailAlloc_6077_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6077_, 0, v___x_6065_);
lean_ctor_set(v_reuseFailAlloc_6077_, 1, v___x_6068_);
lean_ctor_set(v_reuseFailAlloc_6077_, 2, v_revDeps_6012_);
v___x_6070_ = v_reuseFailAlloc_6077_;
goto v_reusejp_6069_;
}
v_reusejp_6069_:
{
lean_object* v___x_6072_; 
if (v_isShared_6064_ == 0)
{
lean_ctor_set(v___x_6063_, 1, v_fst_6057_);
v___x_6072_ = v___x_6063_;
goto v_reusejp_6071_;
}
else
{
lean_object* v_reuseFailAlloc_6076_; 
v_reuseFailAlloc_6076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6076_, 0, v_fst_6061_);
lean_ctor_set(v_reuseFailAlloc_6076_, 1, v_fst_6057_);
v___x_6072_ = v_reuseFailAlloc_6076_;
goto v_reusejp_6071_;
}
v_reusejp_6071_:
{
lean_object* v___x_6074_; 
if (v_isShared_6060_ == 0)
{
lean_ctor_set(v___x_6059_, 1, v___x_6072_);
lean_ctor_set(v___x_6059_, 0, v___x_6070_);
v___x_6074_ = v___x_6059_;
goto v_reusejp_6073_;
}
else
{
lean_object* v_reuseFailAlloc_6075_; 
v_reuseFailAlloc_6075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6075_, 0, v___x_6070_);
lean_ctor_set(v_reuseFailAlloc_6075_, 1, v___x_6072_);
v___x_6074_ = v_reuseFailAlloc_6075_;
goto v_reusejp_6073_;
}
v_reusejp_6073_:
{
return v___x_6074_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6098_, lean_object* v___x_6099_, lean_object* v_fixedParamPerms_6100_, lean_object* v_next_6101_, lean_object* v_inst_6102_, lean_object* v_R_6103_, lean_object* v_a_6104_, lean_object* v_b_6105_, lean_object* v_c_6106_){
_start:
{
lean_object* v___x_6107_; 
v___x_6107_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6098_, v___x_6099_, v_fixedParamPerms_6100_, v_next_6101_, v_a_6104_, v_b_6105_);
return v___x_6107_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6108_, lean_object* v___x_6109_, lean_object* v_fixedParamPerms_6110_, lean_object* v_next_6111_, lean_object* v_inst_6112_, lean_object* v_R_6113_, lean_object* v_a_6114_, lean_object* v_b_6115_, lean_object* v_c_6116_){
_start:
{
lean_object* v_res_6117_; 
v_res_6117_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6108_, v___x_6109_, v_fixedParamPerms_6110_, v_next_6111_, v_inst_6112_, v_R_6113_, v_a_6114_, v_b_6115_, v_c_6116_);
lean_dec(v_next_6111_);
lean_dec_ref(v_fixedParamPerms_6110_);
lean_dec_ref(v___x_6109_);
lean_dec(v_upperBound_6108_);
return v_res_6117_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6118_, lean_object* v___x_6119_, lean_object* v_fixedParamPerms_6120_, lean_object* v_inst_6121_, lean_object* v_R_6122_, lean_object* v_a_6123_, lean_object* v_b_6124_, lean_object* v_c_6125_){
_start:
{
lean_object* v___x_6126_; 
v___x_6126_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6118_, v___x_6119_, v_fixedParamPerms_6120_, v_a_6123_, v_b_6124_);
return v___x_6126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6127_, lean_object* v___x_6128_, lean_object* v_fixedParamPerms_6129_, lean_object* v_inst_6130_, lean_object* v_R_6131_, lean_object* v_a_6132_, lean_object* v_b_6133_, lean_object* v_c_6134_){
_start:
{
lean_object* v_res_6135_; 
v_res_6135_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6127_, v___x_6128_, v_fixedParamPerms_6129_, v_inst_6130_, v_R_6131_, v_a_6132_, v_b_6133_, v_c_6134_);
lean_dec_ref(v_fixedParamPerms_6129_);
lean_dec_ref(v___x_6128_);
lean_dec(v_upperBound_6127_);
return v_res_6135_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6136_, lean_object* v_inst_6137_, lean_object* v_R_6138_, lean_object* v_a_6139_, lean_object* v_b_6140_, lean_object* v_c_6141_){
_start:
{
lean_object* v___x_6142_; 
v___x_6142_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6136_, v_a_6139_, v_b_6140_);
return v___x_6142_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6143_, lean_object* v_inst_6144_, lean_object* v_R_6145_, lean_object* v_a_6146_, lean_object* v_b_6147_, lean_object* v_c_6148_){
_start:
{
lean_object* v_res_6149_; 
v_res_6149_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6143_, v_inst_6144_, v_R_6145_, v_a_6146_, v_b_6147_, v_c_6148_);
lean_dec(v_upperBound_6143_);
return v_res_6149_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6150_, lean_object* v_inst_6151_, lean_object* v_R_6152_, lean_object* v_a_6153_, lean_object* v_b_6154_, lean_object* v_c_6155_){
_start:
{
lean_object* v___x_6156_; 
v___x_6156_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6150_, v_a_6153_, v_b_6154_);
return v___x_6156_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6157_, lean_object* v_inst_6158_, lean_object* v_R_6159_, lean_object* v_a_6160_, lean_object* v_b_6161_, lean_object* v_c_6162_){
_start:
{
lean_object* v_res_6163_; 
v_res_6163_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6157_, v_inst_6158_, v_R_6159_, v_a_6160_, v_b_6161_, v_c_6162_);
lean_dec(v_upperBound_6157_);
return v_res_6163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6221_; uint8_t v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; 
v___x_6221_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6222_ = 0;
v___x_6223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6224_ = l_Lean_registerTraceClass(v___x_6221_, v___x_6222_, v___x_6223_);
return v___x_6224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6225_){
_start:
{
lean_object* v_res_6226_; 
v_res_6226_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6226_;
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
